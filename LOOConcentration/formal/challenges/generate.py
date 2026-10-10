#!/usr/bin/env python3
"""Deterministic packaging of the four revised manuscript frozen result declarations."""
from pathlib import Path
import argparse
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
REPO = PROJECT.parent.parent
NAMES = ['simplifiedConcentration', 'mainConcentration', 'looMoments', 'dataDependentConcentration']
PAPER_RESULTS = ['Theorem 1', 'Theorem 2', 'Corollary 1', 'Theorem 3']
NAMESPACE = 'LOOConcentration.Revision.Challenges'

def sha(data):
    return hashlib.sha256(data).hexdigest()

def anchors():
    manifest = json.loads((PROJECT / 'revision-anchors.json').read_text())
    by_export = {a['export']: a for a in manifest['anchors']}
    result = []
    for name, paper_result in zip(NAMES, PAPER_RESULTS):
        approved = by_export['LOOConcentration.Revision.' + name]
        path = PROJECT / approved['path']
        data = path.read_bytes()
        if sha(data) != approved['sha256']:
            raise ValueError('Revised frozen source hash mismatch: ' + approved['path'])
        text = data.decode('utf-8')
        start = text.index('theorem ' + name)
        command = text[start:text.rindex('\nend LOOConcentration.Revision')].rstrip('\n')
        header, sep, body = command.rpartition(' := by')
        if not sep:
            raise ValueError('Unsupported frozen proof boundary: ' + name)
        imports = re.findall(r'^import ([\w.]+)$', text, re.M)
        a = dict(id=approved['export'], export=approved['export'],
                 path='LOOConcentration/formal/' + approved['path'],
                 file_sha256=approved['sha256'],
                 source=dict(manuscript_sha256=approved['source_sha256'], paper_result=paper_result))
        result.append(dict(anchor=a, name=name, header=header,
                           body='  ' + body.strip(), imports=imports))
    return result

def preamble(imports):
    return '\n'.join('import ' + m for m in sorted(set(imports))) + '''\n\nset_option autoImplicit false
namespace LOOConcentration.Revision.Challenges
open LOOConcentration LOOConcentration.Revision MeasureTheory Filter
open scoped Topology ENNReal

'''

def templates():
    items = anchors()
    imports = {m for x in items for m in x['imports']}
    challenge_imports = sorted(m for m in imports
                               if not m.startswith('LOOConcentrationRevision.Providers.Results.'))
    challenge = preamble(challenge_imports)
    solution = preamble(imports)
    for x in items:
        challenge += x['header'] + ' := by\n  sorry\n\n'
        solution += x['header'] + ' := by\n' + x['body'] + '\n\n'
    footer = 'end LOOConcentration.Revision.Challenges\n'
    return challenge + footer, solution + footer, items

def closure(imports):
    seen = set()
    todo = list(imports)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        f = PROJECT / (m.replace('.', '/') + '.lean')
        if not f.is_file():
            if m.startswith(('LOOConcentration.', 'LOOConcentrationRevision.', 'LOOConcentrationManuscript.')):
                raise ValueError('Missing project import: ' + m)
            continue
        seen.add(m)
        todo.extend(re.findall(r'^import ([\w.]+)$', f.read_text(), re.M))
    return seen

def manifest_data():
    challenge, solution, items = templates()
    ci = re.findall(r'^import ([\w.]+)$', challenge, re.M)
    si = re.findall(r'^import ([\w.]+)$', solution, re.M)
    deps = closure(ci)
    leaked = sorted(m for m in deps if m.startswith(
        ('LOOConcentration.Results.Providers.', 'LOOConcentration.Frozen.Results.', 'LOOConcentrationRevision.Providers.Results.', 'LOOConcentrationRevision.Frozen.Results.')))
    if leaked:
        raise ValueError('Challenge imports result proofs: ' + ', '.join(leaked))
    providers = sorted(m for m in closure(si)
                       if m.startswith(('LOOConcentration.Frozen.Results.', 'LOOConcentrationRevision.Frozen.Results.')))
    support = HERE / 'ComparatorSupport.lean'
    return dict(schema_version=1,
                role='Exercise packaging; not new frozen anchors or proof progress',
                namespace=NAMESPACE,
                frozen_manifest_sha256=sha((PROJECT / 'revision-anchors.json').read_bytes()),
                lean_toolchain=(PROJECT / 'lean-toolchain').read_text().strip(),
                lake_manifest_sha256=sha((PROJECT / 'lake-manifest.json').read_bytes()),
                challenge_sha256=sha(challenge.encode()),
                reference_solution_sha256=sha(solution.encode()),
                comparator_support_sha256=sha(support.read_bytes()),
                challenge_imports=ci, solution_imports=si,
                challenge_project_closure=sorted(deps),
                challenge_project_source_sha256={m: sha((PROJECT / (m.replace('.', '/') + '.lean')).read_bytes()) for m in sorted(deps)},
                solution_project_source_sha256={m: sha((PROJECT / (m.replace('.', '/') + '.lean')).read_bytes()) for m in sorted(closure(si))},
                solution_frozen_result_dependencies=providers,
                permitted_axioms=['propext', 'Classical.choice', 'Quot.sound'],
                authorized_exercise_holes=[dict(file='challenges/Challenge.lean',
                    export=NAMESPACE + '.' + x['name'], body='by\n  sorry',
                    status='EXERCISE_UNPROVED') for x in items],
                targets=[dict(anchor_id=x['anchor']['id'],
                    frozen_export=x['anchor']['export'],
                    exercise_export=NAMESPACE + '.' + x['name'],
                    frozen_path=x['anchor']['path'],
                    frozen_file_sha256=x['anchor']['file_sha256'],
                    header_sha256=sha(x['header'].encode()),
                    source=x['anchor']['source']) for x in items])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write-template-files', action='store_true',
                        help='Generate both templates from the protected sources.')
    parser.add_argument('--write-manifest', action='store_true',
                        help='Write manifest after support and templates exist.')
    args = parser.parse_args()
    challenge, solution, _ = templates()
    if args.write_template_files:
        (HERE / 'Challenge.lean').write_text(challenge)
        (HERE / 'Solution.lean').write_text(solution)
    if args.write_manifest:
        if (HERE / 'Challenge.lean').read_text() != challenge:
            raise ValueError('Challenge differs from generated exact template')
        if (HERE / 'Solution.lean').read_text() != solution:
            raise ValueError('Reference solution differs from frozen assembly')
        (HERE / 'manifest.json').write_text(json.dumps(manifest_data(), indent=2) + '\n')
    if not (args.write_template_files or args.write_manifest):
        if (HERE / 'Challenge.lean').read_text() != challenge:
            raise ValueError('Challenge template drift')
        if (HERE / 'Solution.lean').read_text() != solution:
            raise ValueError('Reference solution drift')
        if json.loads((HERE / 'manifest.json').read_text()) != manifest_data():
            raise ValueError('Challenge manifest drift')
        print('PASS: exact templates, frozen bindings, support pin and challenge isolation')

if __name__ == '__main__':
    main()
