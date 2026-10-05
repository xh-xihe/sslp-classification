"""Review both literal SI count tables and the new physical formula bridges."""
import argparse
import hashlib
import json
from pathlib import Path

from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
T = 'MainTheory.SupplementarySectorCounts.'
W = 'MainTheory.Generated.SupplementarySectorWitnesses.'
B = 'MainTheory.SupplementarySectorCountBase.'
H = 'MainTheory.Generated.SupplementarySectorHeaders.'
O = 'MainTheory.SupplementaryOrderTwoReduction.'
S = 'MainTheory.Orbit3PrintedSpinTrace.'
P = 'MainTheory.Orbit26PrintedProbabilities.'
GROUPS = [
    (['tab:angle-record-counts'],
     [T+'angleRow',T+'angle_table',T+'angle_totals',B+'recordSector',
      B+'selectedRecords_eq_list',B+'recordCount_eq_list']+
     [W+s+'Records_complete' for s in ['coarse','feasible','compatible']],
     'Compared all fourteen (q,m) rows, delta=q/m, and all six total columns. '
     'The raw, primitive and nonempty counts use the exact outer enumeration. '
     'Every subsequent count is the cardinality of the actual surviving '
     'record set filtered by its actual generated record q/m fields. Kernel '
     'membership and no-repetition proofs, together with the already proved '
     'total cardinalities, establish completeness of the smaller witness '
     'lists. Duplicated angle records are retained; no copied per-sector '
     'Python count replaces the semantic record count.'),
    (['tab:fiber-pair-counts'],
     [T+'pairRow',T+'pair_table',T+'pair_totals',T+'orbitCount',
      B+'pairCount',B+'pairCount_eq_list',B+'allPairCount_eq_interval',H+'header_spec']+
     [W+s+'Pairs_source' for s in ['coarse','feasible','compatible']]+
     [W+s+'Pairs_nodup' for s in ['coarse','feasible','compatible']]+
     ['MainTheory.Generated.FinitePairProvenance.validity',
      'MainTheory.Generated.FinitePairDistinctness.pairAtId_injective',
      'MainTheory.Generated.FiniteOrbitCertificate.directory_valid'],
     'Compared all fourteen (q,m) rows and all five total columns. Counts '
     'refer to sets of actual full fibre-pair payloads. Exact provenance '
     'supplies both directions and an injective lookup proves distinct '
     'pair indices carry distinct payloads. Stage id lists are connected '
     'exactly to the original coarse/moment/rank lists and proved to have '
     'no repetitions. All 11422 actual q/m headers are independently checked '
     'in bounded kernel decisions; sector intervals then give the nonempty '
     'pair counts. Orbit counts read q AND m from the actual complete and '
     'pairwise-inequivalent 66-key directory; this is distinct from the '
     'main table grouped only by logical order m.'),
    (['cor:m2-eleven-remaining','eq:m2-eleven-remaining'],
     [O+'order_two_count',O+'order_two_partition',O+'exact_reduction',
      O+'excluded_no_completion',O+'image_scope',
      'MainTheory.SupplementaryImageStatus.provedImages_eq'],
     'The actual directory has 25 logical-order-two keys, and the explicit '
     '14 excluded paper ids and 11 retained ids partition them. Exact '
     'HasCompletion is equivalent to membership in the printed eleven-id '
     'set under the actual logical-order-two hypothesis. Of those eleven, '
     'the updated proved-image set intersects in the nine printed settled '
     'ids 2,3,10,11,16,21,22,23,45; its complement is precisely 1 and 4. '
     'The existence classification is not substituted for an unknown '
     'weight-enumerator image converse.'),
    (['o3gc:spinzero'],
     [S+'bilinear',S+'bilinear_eq',S+'pairing_symmetric',S+'pairing_diagonal_zero',
      S+'trace_formula',S+'sqrt_two_spin',S+'bilinear_normalized',S+'raw_parity',
      S+'raw_spin',S+'raw_trace',
      'MainTheory.Orbit8SpinProjector.spin_conjugate_action'],
     'The bilinear is the actual six-site Y tensor with no conjugation on '
     'the left state, including the Hermitian-Pauli sign. The actual odd '
     'parity involution kills both same-parity terms, and symmetry equates '
     'the two mixed terms. The sqrt-two superposition therefore has '
     's(w)=u^T S v. The normalized actual projector and its spin conjugate '
     'have trace 2*normSq(u^T S v)/N^2 for arbitrary positive common norm N. '
     'No individual amplitude is divided out; the operator identity does '
     'not use the final A3-vanishing theorem.'),
    (['eq:q4o26weights'],
     [P+'P',P+'Q',P+'bottom_native',P+'top_native',P+'physical_probabilities',
      'MainTheory.OrderFour26Moments.pattern'],
     'All eight aggregate probabilities of the actual supported codewords '
     'have the literal two-parameter pattern under normalized physical KL. '
     'The bottom/top ordering is kernel-checked against the native physical '
     'fibres; alpha=P3 and beta=P5 are retained in the printed order. The '
     'derivation uses the physical diagonal moment equations, rather than '
     'the final no-code conclusion, and permits every zero-amplitude face.'),
    (['eq:q4o26paritysums'],
     [P+'physical_parity_sums',P+'physical_probabilities'],
     'Both displayed aggregate parity sums are 3/8 for the actual supported '
     'complex codewords. They follow directly from the physical moment '
     'normal form, with the same normalization and KL hypotheses.'),
]

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply',action='store_true')
    args = parser.parse_args()
    path = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-sector-tables.json'
    types = json.loads(path.read_text(encoding='utf8'))
    if types['sources_sha256'] != SOURCES:
        raise ValueError('Type evidence source binding changed')
    missing = {n for g in GROUPS for n in g[1]}-{r['name'] for r in types['declarations']}
    if missing:
        raise ValueError('Uninspected types: '+str(missing))
    apply_reviews('supplementary',GROUPS,'sector-tables-review',args.apply,
                  expected_sources=SOURCES,review_prefix='20261005 sector table/physical formula type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (path.parent/'sector-tables-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(path.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(path.read_bytes()).hexdigest()
        },indent=2)+'\n',encoding='utf8')
