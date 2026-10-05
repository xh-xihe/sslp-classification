#!/usr/bin/env python3
"""Review the actual new seven-qubit example against its kernel proofs."""
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
import paper_claims
from review_core_claims_20261003 import SOURCES

N = 'MainTheory.SevenQubit'
REVIEWS = {
    'ex:seven-qubit-rationalization': (
        [N + 'PrintedStates.state0_printed', N + 'PrintedStates.state1_printed',
         N + 'ExampleStates.hasDistance_two', N + 'ExampleStates.not_hasDistance_three',
         N + 'ExampleProjector.preserving_phases', N + 'ExampleProjector.real_kernel',
         N + 'LogicalCharacter.projectiveEquiv', N + 'RationalFamily.family_infinite_order',
         N + 'LogicalAction.family_eigenvalues', N + 'MinimumOrder.minimum_physical_order'],
        'The complete current example is attached to its actual seven-qubit complex states and orthogonal projector. Their displayed coefficients, full distance-two KL, distance-three obstruction, preserving circle phases, real edge kernel, projective group ZMod 6, literal family eigenvalues, irrational infinite physical order and exact minimum physical order 12 are proved for this code. The older five-qubit example is not used as a substitute.'),
    'eq:example-zero-L': ([N + 'PrintedStates.state0_printed', N + 'PrintedStates.state1_printed'],
        'Both align rows were read in this inventory block. The four tensor-product ket coefficients of state zero are 1/(sqrt 2 sqrt 3) twice and sqrt 2/(sqrt 2 sqrt 3) twice; state one has the six printed disjoint strings with coefficient 1/sqrt 6. Numeric mask bit j is printed coordinate j+1, so the listed masks were checked in this coordinate order.'),
    'eq:example-common-mean': ([N + 'ExampleStates.first_moments', N + 'ExampleProjector.detects_single_Z'],
        'The actual squared complex amplitudes have moments [1/2,1/2,1/2,1/2,2/3,2/3,2/3]. Full weight-one X,Y,Z KL was also checked, not inferred from the first moments alone.'),
    'displaymath@910': ([N + 'ExampleStates.zz12_expectations', N + 'ExampleStates.not_hasDistance_three'],
        'The literal Z on printed coordinates one and two has weight two and expectations 1 and -1/3 in the actual states; it obstructs distance three.'),
    'displaymath@920': ([N + 'ExampleProjector.preserving_phases'],
        'Actual projector preservation is equivalent to the displayed circle-valued pattern, together with 4 alpha=0 and 3 beta=0. This is a solved equality, not an assumed parametrization.'),
    'displaymath@927': ([N + 'ExampleData.direction', N + 'PhaseArithmetic.pattern'],
        'The direction is exactly [1,-1,0,0,1,-1,0]; the zero-u pattern is the displayed four alpha and three beta entries.'),
    'eq:example-physical-group': ([N + 'ExampleProjector.preserving_phases',
        N + 'CharacterArithmetic.torsion_preimage'],
        'All preserving phases have exactly the pattern with alpha in the fourth-root subgroup and beta in the third-root subgroup. The circle torsion preimage theorem supplies the quarter and third rational representatives; arbitrary circle u has a real lift.'),
    'displaymath@946': ([N + 'ExampleData.direction_zero'],
        'Every string in either actual nonzero support has literal integer dot product zero with the displayed direction.'),
    'eq:example-kernel': ([N + 'ExampleProjector.real_kernel'],
        'The actual nonzero-entry edge matrix of the actual projector has real kernel exactly the one-dimensional line spanned by the displayed direction.'),
    'eq:example-kernel-identity': ([N + 'RationalFamily.direction_identity', N + 'ExampleData.direction_mean'],
        'The actual diagonal matrix at u v multiplies the actual projector to itself for every real u; the direction also has zero common-mean dot product.'),
    'eq:example-logical-map': ([N + 'LogicalAction.state0_eigen', N + 'LogicalAction.state1_eigen',
        N + 'LogicalCharacter.pattern_character'],
        'In the actual displayed logical eigenbasis the physical preserving gate has eigenvalues one and the unit-circle phase of 2 alpha+2 beta. The circle exponential bridge supplies the written exponential.'),
    'displaymath@977': ([N + 'CharacterArithmetic.chi', N + 'CharacterArithmetic.circle_character',
        N + 'CharacterArithmetic.chi_surjective', N + 'CharacterArithmetic.chi_kernel'],
        'The exact character is 3a+4b modulo six. Its addition law, surjectivity and the two-element kernel are finite propositions checked by the Lean kernel.'),
    'eq:example-logical-group': ([N + 'LogicalCharacter.projectiveEquiv',
        N + 'CharacterArithmetic.chi_surjective', N + 'CharacterArithmetic.chi_kernel'],
        'An injective actual projective logical character factors to a bijective additive map onto ZMod 6. This identifies the actual projector quotient, not only an abstract finite arithmetic table.'),
    'eq:example-rational-theta-prime': ([N + 'MinimumOrder.angle12',
        N + 'MinimumOrder.phase_pattern', N + 'MinimumOrder.angle12_primitive', N + 'MinimumOrder.physical_order'],
        'The actual reduced phase has numerator vector [3,3,3,3,4,4,4] modulo twelve. Its literal gcd is one and its physical diagonal matrix has order exactly twelve.'),
    'eq:example-one-parameter-family': ([N + 'RationalFamily.theta_formula', N + 'RationalFamily.theta0_phase'],
        'The exact real formula theta0+t v agrees coordinatewise with the printed quarter/third vector and with the reduced modulus-twelve physical phase.'),
    'eq:example-logical-action': ([N + 'LogicalAction.family_eigenvalues',
        N + 'MinimumOrder.logical_order', N + 'RationalFamily.family_class', N + 'RationalFamily.family_infinite_order'],
        'Every real parameter gives the stated actual basis action diag(1, exp(2*pi*i/6)) and the same projective class of order six. Irrational t has infinite actual physical matrix order.'),
    'eq:example-target-congruence': ([N + 'CharacterArithmetic.circle_character',
        N + 'CharacterArithmetic.target_gcds', N + 'CharacterArithmetic.circle_target_orders'],
        'The target relative phase is exactly chi(a,b)=1. The kernel-checked finite arithmetic forces alpha to have order four and beta to have order three.'),
    'eq:example-minimum-order-gap': ([N + 'MinimumOrder.twelve_dvd_representative',
        N + 'MinimumOrder.minimum_physical_order', N + 'MinimumOrder.logical_order'],
        'For every reduced finite physical representative of this same actual projective class, twelve divides its order. The explicit representative attains twelve, so the true minimum is twelve and is greater than the logical order six.'),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--apply', action='store_true')
    args = parser.parse_args()
    art = ROOT / 'artifacts/orbit-certification-20261003'
    for name in ('seven-qubit-states-build.json', 'seven-qubit-projector-and-character-build.json',
                 'seven-qubit-logical-character-build.json', 'seven-qubit-rational-family-build.json',
                 'seven-qubit-printed-states-build.json', 'seven-qubit-logical-action-build.json'):
        if json.loads((art / name).read_text(encoding='utf8'))['status'] != 'PASS':
            raise ValueError('Unpassed physical-example proof: ' + name)
    path = ROOT / 'results/paper-claims-20261003.json'
    ledger = json.loads(path.read_text(encoding='utf8'))
    paper_claims.validate(ledger, sources=paper_claims.sources_for_version('20261003'))
    if ledger['sources'] != SOURCES:
        raise ValueError('The reviewed manuscript context changed')
    decisions = []
    for entry in ledger['claims']:
        if not entry['id'].startswith('main.tex:'):
            continue
        suffix = entry['id'].removeprefix('main.tex:')
        if suffix not in REVIEWS:
            continue
        names, review = REVIEWS[suffix]
        entry.update(status='covered', lean_declarations=names,
                     review='20261003 current-source review (2026-10-04): ' + review)
        decisions.append({k: entry[k] for k in ('id', 'statement_sha256', 'status', 'lean_declarations', 'review')})
    if len(decisions) != len(REVIEWS):
        raise ValueError('Missing reviewed seven-qubit statement')
    if args.apply:
        path.write_text(json.dumps(ledger, ensure_ascii=False, indent=2) + '\n', encoding='utf8')
        (art / 'seven-qubit-correspondence-review.json').write_text(
            json.dumps({'schema': 1, 'sources': SOURCES, 'claims': decisions}, ensure_ascii=False, indent=2) + '\n',
            encoding='utf8')
    print('Reviewed current-source actual seven-qubit claims:', len(decisions))


if __name__ == '__main__':
    main()
