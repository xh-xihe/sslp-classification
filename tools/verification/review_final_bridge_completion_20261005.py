"""Review the three final SI displays against fresh actual physical kernel types."""
import argparse
import hashlib
import json
from pathlib import Path
from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
D = ROOT / 'artifacts/manuscript-certification-20261005'

def roots(module, *names):
    return ['MainTheory.' + module + '.' + name for name in names]

GROUPS = [
    (['eq:o5-schmidt'], roots('ComplexSchmidtDecomposition', 'orthogonal_rows', 'left_orthogonal_rows', 'schmidt') +
     roots('Orbit5SchmidtCompletion', 'gram_trace_unitary', 'coefficient_gram_trace', 'diagonal_gram_trace', 'normalized_schmidt', 'physical_schmidt'),
     'Actual local complex unitaries diagonalize every two-by-two coefficient matrix, including both singular branches. The actual physical anchor norm is one third. Unitary Gram-trace invariance gives nonnegative real s,t with s squared plus t squared equal to one and the literal inverse-square-root-of-three scale in the printed Schmidt form. No final orbit contradiction is used.'),
    (['eq:o14-orthogonalframes'], roots('Orbit14SliceGeometry', 'positive_common_neighbor', 'common_orthogonal_wedge', 'balanced_slice_frames') +
     roots('Orbit14OrthogonalFrames', 'actual_adjacency', 'physical_mass_rows', 'physical_positive_block', 'physical_orthogonal_frames'),
     'The actual native physical KL moment rows give equal positive chosen-block masses and complementary pointwise balances. All actual offdiagonal slice spinors are orthogonal by the weight-at-most-two physical incidence rows. A positive common neighbor puts the actual bottom spinors on one unit line and all top spinors on its orthogonal line. Their actual block frames are respectively mu times the rank-one projector and mu times its orthogonal complement, before using the separate KL block-frame equality. This direct incidence proof proves the printed intermediate without claiming it follows from the final no-code theorem.'),
    (['q2fam:eq:split-orbits'], roots('SplitFamilyLogicalCompletion', 'raw_logical', 'seed_logical', 'W_isometry', 'W_logical', 'split_logical', 'physical_factors', 'encoder_logical', 'encoder_isometry', 'encoder_distance') +
     roots('SplitFamilyTableCertification', 'pauli_label', 'gate_eq_pauli', 'encoder_orthonormal', 'encoder_gate', 'inverse_coordinates', 'table_angles', 'table_primitive', 'logical_values_distinct', 'table_distance', 'table_orthonormal', 'table_gate'),
     'All four actual split encoders, with the weight-three or weight-five logical seed and the actual W2 or W3 matrix, satisfy full physical weight-at-most-two KL for every real parameter. The explicit six-coordinate permutations give exactly the four sorted SI angle records. The literal physical diagonal gate has logical eigenvalues plus and minus one on orthonormal code words. The table changes logical seed basis where stated in the manuscript; it does not assume a single displayed seed basis realizes all four rows simultaneously.'),
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    for phase in ('final-bridge-completion-full-build-v1', 'final-bridge-completion-type-inspection-v1'):
        assert json.loads((D / (phase + '-exit.json')).read_text(encoding='utf8'))['exit_code'] == 0, phase
    path = D / 'kernel-types-final-bridge-completion-v1.json'
    types = json.loads(path.read_text(encoding='utf8'))
    assert types['sources_sha256'] == SOURCES
    missing = {n for _, names, _ in GROUPS for n in names} - {r['name'] for r in types['declarations']}
    assert not missing, sorted(missing)
    apply_reviews('supplementary', GROUPS, 'final-bridge-completion-review-v1', args.apply,
                  expected_sources=SOURCES, review_prefix='20261005 final actual bridge type/context review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (D / 'final-bridge-completion-type-binding-v1.json').write_text(json.dumps({
            'sources_sha256': SOURCES, 'type_evidence': path.relative_to(ROOT).as_posix(),
            'type_evidence_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'scope': 'The three listed actual SI intermediates, including singular and boundary cases; frozen main issues retain their dispositions.'}, indent=2) + '\n', encoding='utf8', newline='\n')

if __name__ == '__main__':
    main()
