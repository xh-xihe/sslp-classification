#!/usr/bin/env python3
"""Export actual kernel declaration types for correspondence review.

Candidate mappings are inspection inputs, never coverage decisions. A final
content-validated build and transitive axiom audit remain separate obligations.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
from lean_source import MODULE_NAME

IMPORTS = (
    'MainTheory.KernelDeclarationTypes',
    'MainTheory.ReviewedDeclarationsAudit',
    'MainTheory.OrbitCertificationFinalAudit',
    'MainTheory.Orbit3PrintedAmplitudes',
    'MainTheory.Orbit3PrintedScalarConsequences',
    'MainTheory.Orbit3PrintedEncoderEquations',
    'MainTheory.Orbit3PrintedScalarInequality',
    'MainTheory.OrderTwoHomogeneousEncoders',
    'MainTheory.SupplementaryImageStatus',
    'MainTheory.PrimitiveOrderTwoCatAlgebra',
)


def requested_roots(ledger, candidates=None):
    names = {n for entry in ledger['claims'] for n in entry['lean_declarations']}
    if candidates is not None:
        if candidates['sources_sha256'] != ledger['sources']:
            raise ValueError('Candidate mappings refer to a different manuscript')
        current = {entry['id']: entry for entry in ledger['claims']}
        for entry in candidates['candidates']:
            claim = current.get(entry['current_id'])
            if claim is None or claim['statement_sha256'] != entry['current_statement_sha256']:
                raise ValueError('Changed candidate statement: ' + entry['current_id'])
            names.update(entry['prior_lean_declarations'])
    for name in names:
        if MODULE_NAME.fullmatch(name) is None:
            raise ValueError('Invalid Lean declaration name: ' + name)
    return sorted(names)


def parse_types(output, expected):
    records = {}
    for line in output.splitlines():
        if not line.strip():
            continue
        message = json.loads(line)
        if message.get('severity') == 'error':
            raise ValueError('Lean rejected type export: ' + message.get('data', ''))
        data = message.get('data', '')
        if data.startswith('CERTIFICATION_TYPE '):
            record = json.loads(data[len('CERTIFICATION_TYPE '):])
            name = record['name']
            if name in records or not record.get('type'):
                raise ValueError('Duplicate or empty exported type: ' + name)
            records[name] = record
    if set(records) != set(expected):
        raise ValueError('Exported roots differ: ' + str(set(expected) ^ set(records)))
    return [records[name] for name in expected]


def root_imports(names):
    """Add existing module prefixes; namespace names need not be modules."""
    modules = set()
    for name in names:
        parts = name.split('.')[:-1]
        while len(parts) >= 2:
            module = '.'.join(parts)
            if (ROOT.joinpath(*parts).with_suffix('.lean')).is_file():
                modules.add(module)
                break
            parts.pop()
    return sorted(modules)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper-version', default='20261003')
    parser.add_argument('--candidates', type=Path)
    parser.add_argument('--extra-roots', type=Path,
                        help='JSON array of explicitly selected declaration names')
    parser.add_argument('--import', dest='extra_imports', action='append', default=[])
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    ledger = json.loads((ROOT / 'results' / ('paper-claims-' + args.paper_version + '.json')).read_text(encoding='utf8'))
    paper_claims.validate(ledger, sources=paper_claims.sources_for_version(args.paper_version))
    candidates = json.loads(args.candidates.read_text(encoding='utf8')) if args.candidates else None
    names = requested_roots(ledger, candidates)
    if args.extra_roots:
        names = sorted(set(names) | set(json.loads(args.extra_roots.read_text(encoding='utf8'))))
    imports = sorted(set(IMPORTS) | set(root_imports(names)) | set(args.extra_imports))
    for name in names + imports:
        if MODULE_NAME.fullmatch(name) is None:
            raise ValueError('Invalid Lean identifier: ' + name)
    if not names:
        raise ValueError('No declaration roots selected')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    diagnostic = args.output.with_suffix('.lean')
    diagnostic.write_text('\n'.join('import ' + name for name in imports) +
                          '\nset_option maxRecDepth 100000\n' +
                          '\n'.join('#certification_types [\n  ' + ',\n  '.join(names[i:i+32]) + '\n]'
                                    for i in range(0, len(names), 32)) + '\n', encoding='utf8')
    result = subprocess.run(['lake', 'env', 'lean', '-j1', '-DwarningAsError=true', '--json', str(diagnostic)],
                            cwd=ROOT, capture_output=True, encoding='utf8')
    args.output.with_suffix('.log').write_text(result.stdout + result.stderr, encoding='utf8')
    if result.returncode:
        raise ValueError('Lean type inspection failed; see ' + str(args.output.with_suffix('.log')))
    records = parse_types(result.stdout, names)
    # Recheck bindings after Lean returns, rather than publishing mixed inputs.
    paper_claims.validate(ledger, sources=paper_claims.sources_for_version(args.paper_version))
    payload = {'schema': 1, 'sources_sha256': ledger['sources'],
               'purpose': 'Kernel type inspection; semantic coverage requires explicit review.',
               'diagnostic_sha256': hashlib.sha256(diagnostic.read_bytes()).hexdigest(),
               'declarations': records}
    args.output.write_text(json.dumps(payload, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
    print('Exported kernel declaration types:', len(records))


if __name__ == '__main__':
    main()
