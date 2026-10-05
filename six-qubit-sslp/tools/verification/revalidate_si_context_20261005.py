#!/usr/bin/env python3
"""Explicit fixed-snapshot review of retained SI statements and contexts.

The publication edits remove implementation narration and change numbering;
the mathematical premises listed below retain their meanings. Changed tables
and remarks and every previously unreviewed formula are excluded. Identity
matching and kernel type export are supporting checks, not a coverage rule for
future manuscripts.
"""
import argparse
import hashlib
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT=Path(__file__).resolve().parents[2]
CONTEXTS=[
    (1151,'The 0/1 bits, least-significant-first integer convention, full '
     'residue fibers, positive actual support, controlled reduced lift, '
     '21 binary moment features and labeled cube quotient are unchanged. '
     'The paper-key bridge retains every literal orbit index and full-fiber '
     'table statistic. Exact rational LP feasibility still means real '
     'probability feasibility, not full complex KL completion.'),
    (1946,'The order-five proof retains the literal class-36 record, '
     'actual supported normalized complex columns, full distance-three KL, '
     'and the stated physical LU transport. The rigid projector and exact '
     'enumerators are unchanged; zero amplitudes are allowed at input.'),
    (4188,'The order-three positive sections retain their literal records, '
     'support conventions, complete KL hypotheses, normalized A/B values, '
     'closed parameter intervals and actual witness constructions. Equal '
     'enumerators are not promoted to LU classification.'),
    (4497,'The primitive order-two family inclusions retain the same actual '
     'fiber records and closed L/M intervals. Retained reviewed statements '
     'are the previously proved inclusions or split constructions. The '
     'unreviewed literal cat derivation is excluded and receives separate '
     'new proofs and individual decisions.'),
    (5289,'The orbit-two argument keeps the actual normalized encoder, '
     'physical partial traces, common frame, Pauli reflection, complex '
     'quartic coordinates and all twelve physical J equations. Its '
     'conditional quartic certificate is connected to that actual encoder. '
     'The changed spectral-table caption is excluded from this decision.'),
    (6009,'The orbit-three argument keeps the actual parity-supported '
     'complex encoder, positive common column norm, complete scalar '
     'transforms, actual finite encoder average and three-copy PSD moment. '
     'The generated sextic certificates are applied through that moment '
     'bridge. No abstract scalar feasible array or free PSD block is '
     'identified with an actual code. Newly proved literal intermediate '
     'formulas receive separate decisions.'),
    (7172,'The further order-two images retain the same literal gate and '
     'support records, normalized trace convention, full KL hypotheses '
     'and actual closed-image attainment. The class-21 Walsh elimination '
     'is on supported full-KL encoders, not arbitrary affine coefficient '
     'arrays. Historical stabilizer descriptions remain separate obligations.'),
    (7556,'The assembled classification retains the actual intrinsic fixed '
     'basis group, bounded representative of its generator, fifteen '
     'realization keys and 51 no-go keys. Only thirteen nonempty images '
     'are asserted complete; class-1/4 converses and the global enumerator '
     'conjecture remain open. Historical frozen-main annotations are not '
     'used as the current SI image status.'),
    (16126,'The no-go proofs retain their literal orbit records, full '
     'residue fibers, actual supported complex amplitudes and complete '
     'KL equations, allowing all boundary supports. Replacing filenames '
     'by exact finite-check descriptions does not alter any local premise '
     'or infer a no-go from probability feasibility alone. Previously '
     'unreviewed intermediate equalities and changed finite-scope remarks '
     'are excluded; final no-gos do not automatically cover those formulas.'),
    (20000,'The count-table mathematical payloads retain their domains '
     'and stage conventions. Removing the reproduction manual adds no '
     'mathematical assertion. Previously unreviewed tables remain unreviewed.'),
]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    candidates=json.loads((ROOT/'results/correspondence-candidates-20261005.json').read_text(encoding='utf8'))
    types_path=ROOT/'artifacts/manuscript-certification-20261005/kernel-types.json'
    types=json.loads(types_path.read_text(encoding='utf8'))
    ledger=json.loads((ROOT/'results/paper-claims-20261003.json').read_text(encoding='utf8'))
    if candidates['sources_sha256']!=SOURCES or types['sources_sha256']!=SOURCES:
        raise ValueError('Explicit SI snapshot changed')
    if candidates['prior_sources_sha256']['documents/20261003/supplementary.tex']!='56bc2c4fd706659dcd1ca09d56c8d9e83c84a8821d22c1494845d49d8fe66a7d':
        raise ValueError('Unexpected prior reviewed snapshot')
    names={row['name'] for row in types['declarations']}
    claims={row['id']:row for row in ledger['claims']}
    groups=[]
    for entry in candidates['candidates']:
        if not entry['current_id'].startswith('supplementary.tex:') or entry['prior_status'] not in ('covered','expository'):
            continue
        claim=claims[entry['current_id']]
        if claim['statement_sha256']!=entry['current_statement_sha256']:
            raise ValueError('Changed SI assertion: '+claim['id'])
        missing=set(entry['prior_lean_declarations'])-names
        if missing:
            raise ValueError('Uninspected declaration types: '+str(missing))
        if claim['status']!='unreviewed':
            raise ValueError('A separately reviewed row must not be overwritten: '+claim['id'])
        context=next(text for end,text in CONTEXTS if claim['line']<end)
        groups.append(([claim['id'].removeprefix('supplementary.tex:')],
                       entry['prior_lean_declarations'],context+
                       ' Retained statement review: '+entry['prior_review'],entry['prior_status']))
    if len(groups)!=1195:
        raise ValueError('Expected 1192 covered statements and three scope remarks')
    apply_reviews('supplementary',groups,'si-retained-context-review',args.apply,
                  expected_sources=SOURCES,review_prefix='20261005 fixed-context/type revalidation: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (ROOT/'artifacts/manuscript-certification-20261005/si-retained-type-binding.json').write_text(
            json.dumps({'sources_sha256':SOURCES,
                        'kernel_types_sha256':hashlib.sha256(types_path.read_bytes()).hexdigest(),
                        'scope':'Only retained reviewed assertions; new and previously unreviewed statements are excluded.'},indent=2)+'\n',encoding='utf8')


if __name__=='__main__':
    main()
