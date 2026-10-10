#!/usr/bin/env python3
"""Check a proof-only solution against the exact four revised manuscript challenges."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
import generate

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent

class Rejected(ValueError):
    pass

def code_only(text):
    """Blank nested comments and strings while preserving line/column layout."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    line = False
    while i < len(text):
        c = text[i]
        if line:
            if c == '\n':
                line = False
            else:
                out[i] = ' '
            i += 1
        elif depth:
            if text.startswith('/-', i):
                out[i:i+2] = [' ', ' ']; depth += 1; i += 2
            elif text.startswith('-/', i):
                out[i:i+2] = [' ', ' ']; depth -= 1; i += 2
            else:
                if c != '\n': out[i] = ' '
                i += 1
        elif string:
            if c == '\\' and i + 1 < len(text):
                out[i:i+2] = [' ', '\n' if text[i+1] == '\n' else ' ']; i += 2
            else:
                if c != '\n': out[i] = ' '
                if c == '"': string = False
                i += 1
        elif text.startswith('--', i):
            out[i:i+2] = [' ', ' ']; line = True; i += 2
        elif text.startswith('/-', i):
            out[i:i+2] = [' ', ' ']; depth = 1; i += 2
        elif c == '"':
            out[i] = ' '; string = True; i += 1
        else:
            i += 1
    if depth or string:
        raise Rejected('Unterminated source comment/string')
    return ''.join(out)

def validate_package():
    manifest = json.loads((HERE / 'manifest.json').read_text())
    if manifest != generate.manifest_data():
        raise Rejected('Challenge manifest or approved dependency/support pins drifted')
    challenge, reference, items = generate.templates()
    if (HERE / 'Challenge.lean').read_text() != challenge:
        raise Rejected('Challenge differs from the exact approved exercise template')
    leaked = [m for m in generate.closure(manifest['challenge_imports'])
              if m.startswith(('LOOConcentration.Results.Providers.', 'LOOConcentration.Frozen.Results.', 'LOOConcentrationRevision.Providers.Results.', 'LOOConcentrationRevision.Frozen.Results.'))]
    if leaked:
        raise Rejected('Challenge imports result proofs: ' + ', '.join(leaked))
    upstream = PROJECT / '.lake/packages/mathlib'
    expected = json.loads((PROJECT / 'lake-manifest.json').read_text())
    pin = next(x['rev'] for x in expected['packages'] if x['name'] == 'mathlib')
    head = subprocess.check_output(['git', '-C', str(upstream), 'rev-parse', 'HEAD'], text=True).strip()
    dirty = subprocess.check_output(['git', '-C', str(upstream), 'status', '--porcelain'], text=True).strip()
    if head != pin or dirty:
        raise Rejected('Mathlib checkout is not clean at its pinned revision')
    if sum(1 for _ in (upstream / '.lake/build/lib').rglob('*.olean')) < 7000:
        raise Rejected('Mathlib olean guard failed; comparator never rebuilds upstream')
    return manifest, reference, items

def validate_submission(text, reference, items):
    offsets = list(re.finditer(r'^theorem (\w+)', text, re.M))
    if [m.group(1) for m in offsets] != generate.NAMES:
        raise Rejected('Submission must declare exactly the four named targets, in order')
    challenge, _, _ = generate.templates()
    expected_prefixes = {reference[:reference.index('theorem ')],
                         challenge[:challenge.index('theorem ')]}
    if text[:offsets[0].start()] not in expected_prefixes:
        raise Rejected('Submission imports/preamble changed; use a pinned challenge or reference preamble')
    footer = '\n\nend LOOConcentration.Revision.Challenges\n'
    if not text.endswith(footer):
        raise Rejected('Submission namespace/footer changed')
    cleaned = code_only(text)
    forbidden = re.search(r'\b(sorry|admit|sorryAx|axiom|native_decide|unsafe|run_cmd|run_elab|initialize|macro|syntax|elab)\b', cleaned)
    if forbidden:
        raise Rejected('Forbidden solution token: ' + forbidden.group(0))
    if re.search(r'\b(?:maxHeartbeats|maxRecDepth)\b', cleaned):
        raise Rejected('Heartbeat/recursion override is forbidden')
    for i, (m, item) in enumerate(zip(offsets, items)):
        end = offsets[i+1].start() if i+1 < len(offsets) else len(text)-len(footer)
        segment = text[m.start():end]
        expected = item['header'] + ' := by\n'
        if not segment.startswith(expected):
            raise Rejected('Frozen statement/header changed: ' + item['name'])
        body = segment[len(expected):]
        for line in code_only(body).splitlines():
            if line.strip() and not line[0].isspace():
                raise Rejected('Top-level code outside proof body: ' + item['name'])
        if not body.strip():
            raise Rejected('Empty proof body: ' + item['name'])


def imports_of(text):
    return re.findall(r'^import ([\w.]+)$', text, re.M)

def without_imports(text):
    return ''.join(line for line in text.splitlines(keepends=True)
                   if not line.startswith('import '))

def harness(text, support, items, command):
    frozen = [str((generate.REPO / x['anchor']['path']).relative_to(PROJECT))
              .removesuffix('.lean').replace('/', '.') for x in items]
    imports = set(imports_of(text) + imports_of(support) + frozen)
    return ('\n'.join('import ' + m for m in sorted(imports)) + '\n\n' +
            without_imports(support) + '\n' + without_imports(text) + '\n' + command + '\n')


def run_lean(path, name, out, records, expected_holes=0):
    cmd = ['lake', 'env', 'lean', str(path)]
    start = time.monotonic()
    completed = subprocess.run(cmd, cwd=PROJECT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, env=os.environ.copy())
    log = out / (name + '.log')
    log.write_text(completed.stdout)
    holes = len(re.findall(r"declaration uses [`'‘]sorry[`'’]", completed.stdout))
    records.append(dict(stage=name, command=cmd, exit_code=completed.returncode,
                        elapsed_seconds=time.monotonic()-start,
                        authorized_holes=expected_holes, observed_hole_warnings=holes,
                        log=str(log), log_sha256=generate.sha(log.read_bytes())))
    if completed.returncode:
        raise Rejected(name + ' failed; see ' + str(log))
    if holes != expected_holes:
        raise Rejected(name + ': expected ' + str(expected_holes) +
                       ' exercise holes, observed ' + str(holes))
    if expected_holes == 0 and 'sorryAx' in completed.stdout:
        raise Rejected(name + ' reports sorryAx')
    print('PASS: ' + name, flush=True)


def compare(solution, output):
    output.mkdir(parents=True, exist_ok=True)
    records = []
    result = dict(verdict='FAIL', solution=str(solution), checks=records)
    try:
        manifest, reference, items = validate_package()
        text = solution.read_text()
        result['solution_sha256'] = generate.sha(text.encode())
        result['challenge_manifest_sha256'] = generate.sha((HERE / 'manifest.json').read_bytes())
        validate_submission(text, reference, items)
        print('PASS: frozen bindings, challenge isolation and exact submitted headers', flush=True)
        checker = subprocess.run([sys.executable, 'scripts/check_dependency_anchors.py'],
                                 cwd=PROJECT, text=True, stdout=subprocess.PIPE,
                                 stderr=subprocess.STDOUT)
        (output / 'frozen-checker.log').write_text(checker.stdout)
        if checker.returncode:
            raise Rejected('Frozen foundation checker failed')
        with tempfile.TemporaryDirectory(prefix='looconcentration-comparator-') as tmp:
            temp = Path(tmp)
            support = (HERE / 'ComparatorSupport.lean').read_text()
            run_lean(HERE / 'Challenge.lean', 'challenge', output, records, expected_holes=4)
            challenge_harness = temp / 'ChallengeAudit.lean'
            challenge_harness.write_text(harness((HERE / 'Challenge.lean').read_text(),
                                                support, items, '#check_frozen_types'))
            run_lean(challenge_harness, 'challenge-types', output, records, expected_holes=4)
            run_lean(solution, 'solution-standalone', output, records)
            solution_harness = temp / 'SolutionAudit.lean'
            solution_harness.write_text(harness(text, support, items, '#check_frozen_solution'))
            run_lean(solution_harness, 'solution-types-and-axioms', output, records)
            audit_log = (output / 'solution-types-and-axioms.log').read_text()
            for item in items:
                if 'PASS ' + generate.NAMESPACE + '.' + item['name'] not in audit_log:
                    raise Rejected('Missing kernel comparison evidence: ' + item['name'])
        result['verdict'] = 'PASS'
        result['targets'] = manifest['targets']
        result['production_draft_anchors'] = 0
        result['authorized_exercise_holes'] = 4
        result['solution_holes'] = 0
        result['allowed_axioms'] = manifest['permitted_axioms']
    except (ValueError, OSError, subprocess.CalledProcessError, StopIteration) as error:
        result['reason'] = str(error)
        print('FAIL: ' + str(error), file=sys.stderr)
    finally:
        (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solution', type=Path, default=HERE / 'Solution.lean')
    parser.add_argument('--output-dir', type=Path, default=HERE / 'reports/latest')
    args = parser.parse_args()
    result = compare(args.solution.resolve(), args.output_dir.resolve())
    sys.exit(0 if result['verdict'] == 'PASS' else 1)

if __name__ == '__main__':
    main()
