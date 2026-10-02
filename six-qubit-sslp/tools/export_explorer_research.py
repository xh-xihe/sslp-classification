"""Export input-bound Lean source locations and independent Python UI fixtures."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
from explorer import class36

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / 'apps/sslp-explorer'
ROOTS = ['normalized0', 'normalized1', 'orthogonal', 'logical0', 'logical1', 'physical_logical', 'distance']

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    source = (SITE/'public/downloads/Certificate.lean').read_bytes()
    evidence = json.loads((SITE/'public/downloads/evidence.json').read_text())
    digest = hashlib.sha256(source).hexdigest()
    if digest != evidence['kernel']['certificate_sha256']:
        raise ValueError('Certificate and recorded hash differ')
    lines = source.decode('utf-8').splitlines()
    root_lines = {}
    for name in ROOTS:
        locations = [i+1 for i,line in enumerate(lines) if line.startswith(f'theorem {name} ') or line.startswith(f'theorem {name} :')]
        if len(locations) != 1:
            raise ValueError(f'Ambiguous certificate root: {name}')
        root_lines[f'SSLPExplorerCase.{name}'] = locations[0]
    baseline = json.loads((SITE/'public/downloads/case.json').read_text())
    scenarios = []
    for name in ['canonical', 'single_sign_flip', 'logical_basis_i', 'mixed_quarter_phases', 'wrong_gate']:
        instance = copy.deepcopy(baseline)
        phases = [[0]*12, [0]*12]
        if name == 'single_sign_flip': phases[0][0] = 2
        if name == 'logical_basis_i': phases[0] = [1]*12
        if name == 'mixed_quarter_phases': phases = [[j % 4 for j in range(12)], [(j*3+1) % 4 for j in range(12)]]
        for i,word in enumerate(instance['words']):
            for j,item in enumerate(word):
                c = item['coordinates']
                for _ in range(phases[i][j]): c = [-v for v in c[4:]] + c[:4]
                item['coordinates'] = c
        if name == 'wrong_gate': instance['gate']['angles'][4] = 1
        result = class36.exact_checks(instance)
        scenarios.append({'name': name, 'angles': instance['gate']['angles'], 'quarterPhases': phases,
                          'words': instance['words'], 'normalized': result['normalization_and_orthogonality'],
                          'support_matches_target': result['support_matches_gate'], 'kl': result['kl']})
    outputs = {
        'app/data/certificate.json': {'sha256': digest, 'lines': lines, 'roots': root_lines},
        'tests/fixtures/phase-scenarios.json': {'method': 'independent exact Python checker', 'input_sha256': class36.digest(baseline), 'scenarios': scenarios},
    }
    for name,value in outputs.items():
        payload = json.dumps(value, ensure_ascii=False, indent=2 if 'certificate' in name else None).encode() + b'\n'
        path = SITE / name
        if args.check:
            if path.read_bytes() != payload: raise ValueError(f'Stale research export: {name}')
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
    print(json.dumps({'status': 'checked' if args.check else 'exported', 'certificate_roots': len(root_lines), 'independent_scenarios': len(scenarios)}))

if __name__ == '__main__':
    main()
