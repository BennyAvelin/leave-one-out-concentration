#!/usr/bin/env python3
"""Meaningful rejection tests for the frozen challenge/solution comparator."""
from pathlib import Path
import json
import subprocess
import tempfile
from unittest.mock import patch
import compare
import generate

HERE = Path(__file__).resolve().parent
OUT = HERE / 'reports/regressions'

def replace_first_proof(text, items, body):
    marker = items[0]['header'] + ' := by\n'
    start = text.index(marker) + len(marker)
    end = text.index('\n\ntheorem ' + items[1]['name'], start)
    return text[:start] + body + text[end:]

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    manifest, reference, items = compare.validate_package()
    compare.validate_submission(reference, reference, items)
    mutations = {
        'extra-premise': reference.replace('theorem mainConcentration {k m n : ℕ}',
            'theorem mainConcentration {k m n : ℕ} (hidden : True)', 1),
        'changed-conclusion': reference.replace('Pplus ≤', 'Pplus <', 1),
        'proof-hole': replace_first_proof(reference, items, '  sorry'),
        'custom-axiom': reference.replace('open scoped Topology ENNReal\n',
            'open scoped Topology ENNReal\naxiom benchmarkCheat : False\n', 1),
        'unauthorized-import': 'import LOOConcentrationRevision.Frozen.Results.MainConcentration\n' + reference,
    }
    results = []
    for name, text in mutations.items():
        fixture = OUT / (name + '.lean.txt')
        fixture.write_text(text)
        try:
            compare.validate_submission(text, reference, items)
        except compare.Rejected as error:
            results.append(dict(test=name, verdict='PASS_REJECTED', reason=str(error),
                                source_sha256=generate.sha(text.encode())))
            print('PASS: rejected ' + name, flush=True)
        else:
            raise AssertionError('Comparator accepted ' + name)
    stale = dict(manifest, frozen_manifest_sha256='0' * 64)
    with patch.object(generate, 'manifest_data', return_value=stale):
        try:
            compare.validate_package()
        except compare.Rejected as error:
            results.append(dict(test='stale-binding', verdict='PASS_REJECTED', reason=str(error)))
            print('PASS: rejected stale binding', flush=True)
        else:
            raise AssertionError('Comparator accepted stale binding')
    leaked = sorted(m for m in generate.closure(manifest['challenge_imports'] +
                   ['LOOConcentrationRevision.Providers.Results.MainConcentration'])
                   if m.startswith(('LOOConcentration.Results.Providers.', 'LOOConcentration.Frozen.Results.', 'LOOConcentrationRevision.Providers.Results.', 'LOOConcentrationRevision.Frozen.Results.')))
    assert leaked, 'Import-closure guard missed a result-provider dependency'
    results.append(dict(test='transitive-import-detection', verdict='PASS_DETECTED', modules=leaked))
    support = (HERE / 'ComparatorSupport.lean').read_text()
    custom = reference.replace('open scoped Topology ENNReal\n',
        'open scoped Topology ENNReal\naxiom benchmarkCheat : False\n', 1)
    custom = replace_first_proof(custom, items, '  exact False.elim benchmarkCheat')
    kernel_cases = {
        'kernel-extra-premise': mutations['extra-premise'],
        'kernel-sorry': mutations['proof-hole'],
        'kernel-custom-axiom': custom,
    }
    with tempfile.TemporaryDirectory(prefix='looconcentration-comparator-negative-') as tmp:
        temp = Path(tmp)
        for name, text in kernel_cases.items():
            source = temp / 'Submission.lean'
            source.write_text(text)
            standalone = subprocess.run(['lake', 'env', 'lean', str(source)],
                cwd=generate.PROJECT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (OUT / (name + '-standalone.log')).write_text(standalone.stdout)
            assert standalone.returncode == 0, name + ' fixture must independently elaborate'
            audit = temp / 'Audit.lean'
            audit.write_text(compare.harness(text, support, items, '#check_frozen_solution'))
            (OUT / (name + '.lean.txt')).write_text(audit.read_text())
            run = subprocess.run(['lake', 'env', 'lean', str(audit)],
                cwd=generate.PROJECT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            (OUT / (name + '.log')).write_text(run.stdout)
            assert run.returncode != 0, 'Kernel checker accepted ' + name
            expected = 'type' if name == 'kernel-extra-premise' else 'axiom'
            assert expected in run.stdout.lower(), name + ' failed without expected comparison evidence'
            results.append(dict(test=name, verdict='PASS_REJECTED_BY_LEAN',
                fixture_elaboration_exit=standalone.returncode, audit_exit=run.returncode,
                source_sha256=generate.sha(text.encode()), output=run.stdout))
            print('PASS: Lean rejected ' + name + ' after standalone elaboration passed', flush=True)
    (OUT / 'result.json').write_text(json.dumps(dict(verdict='PASS', tests=results), indent=2) + '\n')
    print('PASS: all comparator rejection tests', flush=True)

if __name__ == '__main__':
    main()
