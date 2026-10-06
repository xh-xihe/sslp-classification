import MainTheory.KernelAxiomAudit
import SixQubit.Orbit7Collinear

#certification_axioms [
  SixQubit.Orbit7Universal.scaledOuter_rank,
  SixQubit.Orbit7Universal.scaledOuter_isNonzeroRankOne,
  SixQubit.Orbit7Universal.twoOuterBlocks_rank,
  SixQubit.Orbit7Universal.bloch_add_sq_eq_mass_sq_sub_wedge,
  SixQubit.Orbit7Universal.zero_angle_trace_rows,
  SixQubit.Orbit7Universal.collinear_three_trace_sum,
  SixQubit.Orbit7Universal.collinear_low_bound,
  SixQubit.Orbit7Universal.collinear_enumerator,
  SixQubit.Orbit7Universal.collinear_extreme_outer_eq,
  SixQubit.Orbit7Universal.collinear_ycoord_zero,
  SixQubit.Orbit7Universal.collinear_pair_blocks_normal_form,
  SixQubit.Orbit7Universal.collinear_pairMarginal_normal_form,
  SixQubit.Orbit7Universal.collinear_pair_blocks_rank_one,
  SixQubit.Orbit7Universal.collinear_pair_rank_two_at,
  SixQubit.Orbit7Universal.collinear_has_pair_rank_two
]
