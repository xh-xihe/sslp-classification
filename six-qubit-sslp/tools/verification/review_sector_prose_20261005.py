"""Review the precise running-text scope of the new sector/spin bridges."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'tools'))
import paper_release
from review_sources_20261005 import SOURCES

ROWS = [
    (5594,5595,
     ['MainTheory.Orbit3PrintedSpinTrace.pairing_symmetric',
      'MainTheory.Orbit3PrintedSpinTrace.pairing_diagonal_zero',
      'MainTheory.Orbit3PrintedSpinTrace.raw_parity',
      'MainTheory.Orbit3PrintedSpinTrace.orbit3_odd'],
     'The actual six-Y bilinear is symmetric. Its same-parity terms '
     'vanish under the actual odd orbit-three involution, including zero '
     'amplitudes. The preceding shadow-saturation sentence is outside '
     'this narrowly reviewed block.'),
    (16129,16131,
     ['MainTheory.SupplementarySectorCountBase.recordCount',
      'MainTheory.Generated.SupplementarySectorWitnesses.coarseRecords_complete',
      'MainTheory.Generated.SupplementarySectorWitnesses.feasibleRecords_complete',
      'MainTheory.Generated.SupplementarySectorWitnesses.compatibleRecords_complete',
      'MainTheory.SupplementarySectorCounts.angle_table'],
     'The three final table stages still count the actual primitive angle '
     'records. Distinct records mapped to the same pair remain distinct '
     'in these actual survivor sets.'),
    (16164,16165,
     ['MainTheory.SupplementarySectorCountBase.pairCount',
      'MainTheory.Generated.FinitePairDistinctness.pairAtId_injective',
      'MainTheory.Generated.FiniteOrbitCertificate.directory_valid',
      'MainTheory.SupplementarySectorCounts.pair_table'],
     'The second table counts distinct actual full labelled fibre-pair '
     'payloads after hashing, and inequivalent actual directory keys in '
     'its final column. Both q and m are retained throughout.'),
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args = parser.parse_args()
    if paper_release.source_hashes('20261003',ROOT) != SOURCES:
        raise ValueError('Reviewed source context changed')
    evidence = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-sector-tables.json'
    types = json.loads(evidence.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Type evidence context changed')
    names = {r['name'] for r in types['declarations']}
    missing = {n for row in ROWS for n in row[2]}-names
    if missing:
        raise ValueError('Uninspected types: '+str(missing))
    path = ROOT/'results/prose-review-20261003.json'
    record = json.loads(path.read_text(encoding='utf8'))
    paper_release.validate_review(record,'20261003',ROOT)
    lines = (ROOT/'documents/20261003/supplementary.tex').read_text(encoding='utf8').splitlines()
    reviewed = [{'source':'supplementary.tex','line':lo,'end_line':hi,'kind':'covered',
                 'reason':reason,'declarations':declarations,
                 'origin':'20261005 explicit sector-table/spin context and type review',
                 'context_sha256_lf':hashlib.sha256('\n'.join(lines[lo-1:hi]).encode()).hexdigest()}
                for lo,hi,declarations,reason in ROWS]
    keys = {(r['source'],r['line'],r['end_line']) for r in reviewed}
    record['assertions'] = [r for r in record['assertions']
                            if (r['source'],r['line'],r.get('end_line',r['line'])) not in keys]+reviewed
    record['status'] = 'partial'
    record['remaining'] = ('Complete all other current prose and mathematical correspondence. '
                           'Preserve the five author-held frozen main issues. '
                           'Kernel build and axiom acceptance are recorded separately.')
    paper_release.validate_review(record,'20261003',ROOT)
    if args.apply:
        path.write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf8')
        (evidence.parent/'sector-prose-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest(),
            'reviewed_blocks':reviewed,'scope':'partial current prose only'
        },ensure_ascii=False,indent=2)+'\n',encoding='utf8')
    print('Total explicit current prose blocks:',len(record['assertions']),'status:',record['status'])

if __name__ == '__main__':
    main()
