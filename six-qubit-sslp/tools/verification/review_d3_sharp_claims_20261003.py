#!/usr/bin/env python3
"""Review the literal sharp rank-two bound, including its original-action pivot."""
import argparse
from apply_current_reviews import apply_reviews

GROUPS = [
    (['cor:d3-physical-order-bound', 'eq:d3-full-bound', 'displaymath@2022'],
     ['MainTheory.D3OriginalRealPivot.full_sparse_bound',
      'MainTheory.D3OriginalRealPivot.for_eigenframe',
      'MainTheory.GateGCD.primitive_iff_gcd'],
     'The new construction starts with the supplied real operation and chooses actual-support basis rows, without first taking a coprime power. One output simultaneously retains the original class, full target KL distance, common actual affine rank, binary nonsingular coordinate minor, logical/physical divisibilities and all sharp inequalities. Primitive residues give literal exact physical order.'),
    (['displaymath@1910', 'displaymath@1946'],
     ['MainTheory.GeneralSectorMoments.sectorProbability_eq_projector',
      'MainTheory.GeneralSectorMoments.sectorProbability_sum_eq_one',
      'MainTheory.CodeAffineSpanBridge.supportProbability_pos',
      'MainTheory.CodeAffineSpanBridge.sum_supportProbability_eq_one'],
     'The two distinct eigenspaces in a rank-two code have rank one. Specializing the full sector-projector diagonal formula to rank one gives norm-square probabilities, normalized mass one, and positivity exactly on nonzero eigenvector support. Thus projector support and ordinary eigenvector support agree.'),
    (['displaymath@1918'],
     ['MainTheory.CodeAffineSpanBridge.commonAffineSpan_of_exactCodeFrame',
      'MainTheory.PositiveAffineFunctionExpansion.affineSpan_eq_of_coordinate_squares'],
     'Actual KL distance at least three yields equality of first and second binary moments; expansion gives every literal coordinate affine square. Strict positive support probabilities determine equal real affine spans.'),
    (['eq:d3-qmin'],
     ['MainTheory.D3AffineRankBound.d3_bound_same_class_at_affineRank',
      'MainTheory.GeneralLiftOrder.qMin_le'],
     'The minimization is over primitive physical representatives of this same original class. The existing class-preserving affine-rank theorem supplies a member of that set at most beta_r and beta_n; the new pivot theorem additionally binds divisibility to its own selected matrix.'),
    (['displaymath@1959'],
     ['MainTheory.RealSupportAffineRank.bitPoint_bxor',
      'MainTheory.RealSupportAffineRank.flipLin',
      'MainTheory.RealSupportAffineRank.finrank_direction_image_affine',
      'MainTheory.D3OriginalRealPivot.shifted_eigen'],
     'The coordinate involution is the affine map bitPoint(x0)+flipLin(x0)*x. Its linear part is invertible, preserving affine dimension. The shifted real eigenvalues are exactly ev/c0, so the first is one after discarding the common scalar.'),
    (['displaymath@1986', 'eq:C-theta-prime', 'displaymath@2003'],
     ['MainTheory.D3FreshSparseAssembly.originalPhase_solves',
      'MainTheory.D3FreshSparseAssembly.angle_eq_on_common_actualSupports',
      'MainTheory.D3SparseRationalization.Data.minor',
      'MainTheory.D3SparseRationalization.Data.minor_nonsingular',
      'MainTheory.D3SparseRationalization.Data.selectedSolution_solves',
      'MainTheory.D3SparseRationalization.Data.fullSolution_solves',
      'MainTheory.SparseSmithDisplays.row_difference_zero',
      'MainTheory.D3OriginalRealPivot.for_eigenframe'],
     'Rows are selected from the normalized actual support. The coordinate minor is selected internally from real independence and is nonsingular over Q. Inverse times the integral right-hand side, extended by zero, solves every row. Its angle agrees pointwise on both actual supports, hence has the original logical action.'),
    (['eq:K2-finite-cutoff'],
     ['MainTheory.SSLPCompleteness.completeness_distance_two',
      'MainTheory.SSLPCompleteness.completeness_distance_three',
      'MainTheory.CodeSpec.ExactCode',
      'MainTheory.BetaExists.betaBound_betaOf',
      'MainTheory.D3OriginalRealPivot.full_sparse_bound'],
     'The two target-distance branches retain the source distance and all sorted/gcd-one/full-fiber conditions. Completeness supplies bounded data for every code in the stated symmetry sector; actual orthonormal full-KL completions give the converse. The source-support refinement comes from the same original-action sparse pivot.'),
]

if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--apply', action='store_true')
    apply_reviews('main', GROUPS, 'd3-sharp-correspondence-review', p.parse_args().apply)
