#!/usr/bin/env python3
"""Review the changed spectral-table caption on the actual physical blocks."""
import argparse
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT=Path(__file__).resolve().parents[2]
NAMES=[
    'MainTheory.Orbit2SpectralTable.counts_correct',
    'MainTheory.Orbit2SpectralTable.number_of_blocks',
    'MainTheory.Orbit2SpectralTable.number_of_coordinates',
    'SixQubit.Generated.Orbit2PhysicalSpectra.physical_characteristic_polynomials',
    'Orbit2.checkedBlocks',
    'Orbit2.shifted_coercivity',
]


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args=parser.parse_args()
    types=json.loads((ROOT/'artifacts/manuscript-certification-20261005/kernel-types-expanded.json').read_text(encoding='utf8'))
    if types['sources_sha256']!=SOURCES:
        raise ValueError('The inspected context changed')
    missing=set(NAMES)-{row['name'] for row in types['declarations']}
    if missing:
        raise ValueError('Uninspected declaration types: '+str(missing))
    apply_reviews('supplementary',[(['o2gc:tab-blocks'],NAMES,
        'Compared all seven printed sizes, multiplicities and factored characteristic '
        'polynomials. The 111-block/492-coordinate counts are actual finite counts; '
        'physical_characteristic_polynomials identifies every polynomial with the '
        'actual checkedBlocks matrix, not a disconnected copy. Each checked block '
        'carries a kernel-proved rational LDL certificate for M-4I, so shifted '
        'coercivity supplies positive definiteness for every physical block. The '
        'caption correctly treats the spectral expressions as supplementary '
        'information and uses rational LDL verification for positivity.')],
        'physical-spectral-table-review',args.apply,expected_sources=SOURCES,
        review_prefix='20261005 actual matrix/type review: ',
        evidence_directory='artifacts/manuscript-certification-20261005')
