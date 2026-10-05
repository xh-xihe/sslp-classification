"""Record inspected physical orbit-31 correspondence, retaining unfinished rows."""
import argparse
import hashlib
import json
from pathlib import Path
from apply_current_reviews import apply_reviews
from review_sources_20261005 import SOURCES

ROOT = Path(__file__).resolve().parents[2]
P = 'MainTheory.'
G = P+'Generated.Orbit31DirectTriangles.'
F = P+'Orbit31FinalCross.'
T = P+'Generated.Orbit31PrintedSupportOrbits.'
GROUPS = [
    (['eq:q4o31phaseratio'],
     [P+'Orbit31PhaseRatios.sigma',P+'Orbit31PhaseRatios.physical_equal_probabilities',
      P+'Orbit31PhaseRatios.reconstruct',P+'Orbit31PhaseRatios.unit_norm',
      P+'ComplementPhaseRatios.rho',P+'ComplementPhaseRatios.unit_norm'],
     'The actual paired codeword amplitudes have equal squared magnitudes. '
     'On an active cell rho=d/star(c) has unit norm; sigma=star(d)/c is its '
     'conjugate. Reconstruction star(d)=sigma*c includes zero cells, and unit '
     'norm is asserted only on active cells. The physical equality is derived '
     'from normalized supported codewords and complete distance-three KL.'),
    (['eq:q4o31verticalphase'],
     [P+'Orbit31CrossConsequences.physical_reciprocal',P+'Orbit31CanonicalPhase.vertical_phase'],
     'The twelve actual reciprocal Pauli incidences give equality of phase '
     'ratios when both endpoints are active. The retained nonzero hypotheses '
     'exclude no boundary solution because zero endpoints carry no phase ratio.'),
    (['eq:q4o31weightonesum'],
     [P+'Orbit31CrossConsequences.physical_weight_one_sum',P+'Orbit31CanonicalPhase.weight_one_phase_sum'],
     'Conjugating the three physical single-flip cross rows and reconstructing '
     'the top amplitudes gives exactly the printed bilinear sums. Terms with '
     'zero endpoints vanish automatically.'),
    (['eq:q4o31rectangle'],
     [P+'Orbit31CrossConsequences.physical_rectangles',P+'Orbit31CanonicalPhase.rectangle_phase'],
     'All eighteen actual four-term rectangle equations are derived from '
     'weight-at-most-two physical Paulis and conjugated into the printed '
     'sigma-weighted products. The row and column pairs keep the SI order.'),
    (['eq:q4o31supportcounts'],
     [P+'Orbit31ExactSupportClassification.exact_support_count',
      P+'Orbit31NoSingletonClassification.exact_support_count',
      P+'Orbit31PhaseClassification.exact_count_chain',P+'Orbit31PhaseClassification.physical_survivor',
      P+'Orbit31BalancedMomentIff.feasible_iff_full_moments',P+'Orbit31PhysicalSupportFilters.physical_filters'],
     'All 65536 masks have checked primal-union or strict-support dual '
     'certificates for arbitrary real nonnegative probabilities in the actual '
     'moment system, not only rational points. Exact subtype cardinalities '
     'are 15603, 2903 and 311. The actual canonical cross equations rule out '
     'singleton overlaps and induce the signed graph. Every remaining graph '
     'record has a checked coloring or a checked odd closed walk, and the '
     '2903 records exhaust the first-filter subtype. The seven balanced '
     'equations are equivalent to the complete real MomentSystem.'),
    (['eq:q4o31symmetry'],
     [P+'Orbit31AffineTableGroup.aglTwoIsoSFour',P+'Orbit31AffineTableGroup.productGroupIso',
      P+'Orbit31AffineTableGroup.all_table_actions',P+'Orbit31TableSymmetry.actual_bottom',
      P+'Orbit31TableSymmetry.actual_top',P+'Orbit31TableSymmetry.fibres_preserved',
      P+'Orbit31TableSymmetry.inner_preserved',P+'Orbit31TableSymmetry.distance_preserved'],
     'The actual affine equivalences of F2 squared form a group isomorphic '
     'to all permutations of its four points, with multiplication preserved. '
     'Together with the three-row permutation group this gives the printed '
     'product group. All 144 table actions are realized by physical qubit '
     'permutations and even local-X translations. They preserve both actual '
     'fibers, inner products and the complete physical distance condition.'),
    (['eq:q4o31permanent'],[P+'Orbit31PermanentAlgebra.permanent'],
     'The permanent is defined as the two literal crossed amplitude products '
     'in the SI table coordinates, without conjugation.'),
    (['lem:q4o31permanenttriangle','eq:q4o31oddpermanent'],
     [P+'Orbit31PermanentAlgebra.odd_permanent_triangle'],
     'The three printed complex permanent equations contradict nonzero '
     'entries. The checked division-free combination is 2*r0*s1*s2=0; '
     'it uses only these three equations and the required nonzero factors.'),
    (['eq:q4o31direct23types','equation@12215'],
     [G+f'Type{k:02d}.{name}' for k in (3,6,12)
      for name in ('printed_binding','phase_pattern','permanent_0','permanent_1','permanent_2','physical_no_go')],
     'Each of the literal types 3, 6 and 12 has checked paths in its actual '
     'signed support graph. Substituting the forced signs into the actual '
     'column-(2,3) rectangle rows gives each of the three row-pair permanents '
     'equal to zero after canceling a nonzero phase factor. The physical '
     'wrapper derives all assumptions from actual supported normalized KL.'),
    (['eq:q4o31direct12types','equation@12224'],
     [G+f'Type{k:02d}.{name}' for k in (4,5,7,8,10,11,13,15)
      for name in ('printed_binding','phase_pattern','permanent_0','permanent_1','permanent_2','physical_no_go')],
     'Each of the eight literal types has the printed column-(1,2) '
     'permanent triangle. Every selected endpoint is connected to the phase '
     'anchor by a checked signed path; unrelated isolated active vertices '
     'are not assigned this phase. Actual physical rectangle rows, checked '
     'substitutions and nonzero cancellation yield all three permanents.'),
    (['eq:q4o31type1a'],[G+'Type01.printed_binding',G+'Type01.phase_pattern',
                           F+'Type01.equation1',F+'Type01.equation2',F+'Type01.equation3',F+'Type01.no_go'],
     'The complete three-line align block for type 1 is checked. Its two '
     'weight-one equations and the column-(2,3) rectangle produce the two '
     'mixed dot products and the permanent. Nonzero active entries give '
     'the division-free mixed-triangle contradiction.'),
    (['eq:q4o31finaltable'],[T+'literal_words',G+'Type02.printed_binding',
                                P+'Orbit31CanonicalPhase.AmplitudeSupport'],
     'The literal type-2 support has A and B1 full, B2 active in columns '
     '0,1 and B3 active in columns 2,3. The amplitude-support predicate '
     'requires exactly the twelve displayed entries to be nonzero and '
     'the other four to vanish.'),
    (['eq:q4o31final1'],[G+'Type02.phase_pattern']+[F+'Type02.equation'+str(k) for k in range(1,6)],
     'The complete five-line align block is derived from actual signed paths, '
     'three weight-one sums and two rectangle rows. Type-2 phase signs are '
     'positive in columns 0,1 and negative in columns 2,3; canceling the '
     'nonzero common phase gives precisely the five printed polynomials.'),
    (['equation@12333','equation@12337'],[P+'Orbit31PermanentAlgebra.product_equality']+
      [F+'Type02.equation'+str(k) for k in range(1,5)],
     'The first and second cross equations imply a0*x0=a1*x1, and the '
     'third and fourth imply a2*x2=a3*x3. The proof multiplies by a '
     'nonzero active y or z amplitude, and does not assume a ratio exists '
     'on an inactive position.'),
    (['eq:q4o31commonK'],[P+'Orbit31PermanentAlgebra.common_product',F+'Type02.commonK'],
     'The fifth actual cross equation equates the two previously equal '
     'pairs of products. The theorem supplies a common nonzero K for all '
     'four columns under the exact type-2 amplitude support.'),
    (['eq:q4o31samestate'],[P+'Orbit31FinalSameState.SameStateRow',
                              P+'Orbit31FinalSameState.physical_row',P+'Orbit31FinalSameState.same_state',
                              P+'Orbit31FinalSameState.physical_same_state'],
     'The actual X4X5 flip and its four physical Z dressings yield the '
     'same-state row. Substitution of the proved type-2 phase signs, '
     'zero inactive amplitudes and unit phase norm isolates the literal '
     'star(a0)*a3+star(x3)*x0=0. No final no-code theorem is invoked.'),
    (['eq:q4o31positivecontradiction'],[P+'Orbit31PermanentAlgebra.positive_identity',
                                         P+'Orbit31PermanentAlgebra.positive_contradiction',
                                         P+'Orbit31FinalSameState.final_no_go'],
     'Multiplying the actual same-state row by a0*star(a3), with '
     'a0*x0=a3*x3=K, gives exactly normSq(a0*a3)+normSq(K)=0. '
     'Strict positivity of the active a0*a3 and nonnegativity of normSq(K) '
     'give the final physical support contradiction without division.'),
]


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    evidence = ROOT/'artifacts/manuscript-certification-20261005/kernel-types-orbit31-support.json'
    data = json.loads(evidence.read_text(encoding='utf8'))
    if data['sources_sha256'] != SOURCES:
        raise ValueError('Inspected types have different manuscript bindings')
    missing = {n for g in GROUPS for n in g[1]}-{r['name'] for r in data['declarations']}
    if missing:
        raise ValueError('Uninspected roots: '+str(missing))
    apply_reviews('supplementary',GROUPS,'orbit31-support-review',args.apply,
                  expected_sources=SOURCES,review_prefix='20261005 current orbit-31 physical/type review: ',
                  evidence_directory='artifacts/manuscript-certification-20261005')
    if args.apply:
        (evidence.parent/'orbit31-support-type-binding.json').write_text(json.dumps({
            'sources_sha256':SOURCES,'type_evidence':str(evidence.relative_to(ROOT)),
            'type_evidence_sha256':hashlib.sha256(evidence.read_bytes()).hexdigest()
        },indent=2)+'\n',encoding='utf8')
