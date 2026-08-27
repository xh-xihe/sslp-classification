import MainTheory.Rationalize
import MainTheory.Denominator
import MainTheory.Clearing
import MainTheory.Covariance
import MainTheory.AffineSpan
import MainTheory.D3Bound
import MainTheory.RealGate
import MainTheory.Levels
import MainTheory.WImages
import MainTheory.Gate
import MainTheory.PhaseSector
import MainTheory.Normalize
import MainTheory.Cyclic
import MainTheory.RankTwo

/-!
# Axiom audit for the `main.tex` general theory

Every headline of `MainTheory` is printed here, on the same standard the
six-qubit development is held to: the footprint must be contained in
`{propext, Classical.choice, Quot.sound}`, with no `sorryAx`, no
`ofReduceBool` and no `native_decide`.

`Classical.choice` is expected throughout this library: the retraction of the
structure map is chosen, not constructed.
-/

#print axioms MainTheory.Rationalize.retract
#print axioms MainTheory.Rationalize.retract_algebraMap
#print axioms MainTheory.Rationalize.retract_algebraMap_mul
#print axioms MainTheory.Rationalize.exists_solution_of_exists_solution_ext
#print axioms MainTheory.Rationalize.eq_of_ker_eq_zero
#print axioms MainTheory.Rationalize.pi_solution
#print axioms MainTheory.Rationalize.rationalized_pi_solution

#print axioms MainTheory.Denominator.clears_iff
#print axioms MainTheory.Denominator.lcmDen_pos
#print axioms MainTheory.Denominator.lcmDen_clears
#print axioms MainTheory.Denominator.lcmDen_dvd_of_clears
#print axioms MainTheory.Denominator.liftNum_spec
#print axioms MainTheory.Denominator.eq_one_of_dvd_lcmDen_of_dvd_liftNum
#print axioms MainTheory.Denominator.lcmDen_example
#print axioms MainTheory.Denominator.lift_exists

#print axioms MainTheory.Gate.weight_stdBasis
#print axioms MainTheory.Gate.diag_pow
#print axioms MainTheory.Gate.natCast_mul_weight
#print axioms MainTheory.Gate.dvd_of_forall_mul_eq_zero
#print axioms MainTheory.Gate.pow_eq_one_iff
#print axioms MainTheory.Gate.primitive_orbit21
#print axioms MainTheory.Gate.not_primitive_allEven
#print axioms MainTheory.Gate.orbit21_order

#print axioms MainTheory.PhaseSector.diag_eq_of_eigen
#print axioms MainTheory.PhaseSector.weight_eq_of_eigen
#print axioms MainTheory.PhaseSector.ssCondition_of_eigen
#print axioms MainTheory.PhaseSector.disjoint_of_ne
#print axioms MainTheory.PhaseSector.eigen_of_ssCondition
#print axioms MainTheory.PhaseSector.eigen_iff_ssCondition
#print axioms MainTheory.PhaseSector.exists_eigen
#print axioms MainTheory.PhaseSector.ssCondition_nonvacuous
#print axioms MainTheory.PhaseSector.support_of_ssCondition
#print axioms MainTheory.PhaseSector.support_of_eigen

#print axioms MainTheory.Normalize.flip_flip
#print axioms MainTheory.Normalize.weight_bxor
#print axioms MainTheory.Normalize.weight_flip_self
#print axioms MainTheory.Normalize.addOrderOf_dvd
#print axioms MainTheory.Normalize.exists_unit_reduction_inv
#print axioms MainTheory.Normalize.exists_unit_mul_eq_one
#print axioms MainTheory.Normalize.ssCondition_bxor
#print axioms MainTheory.Normalize.weight_bxor_check

#print axioms MainTheory.Cyclic.chi_zero
#print axioms MainTheory.Cyclic.diag_eq_chi
#print axioms MainTheory.Cyclic.pow_mod
#print axioms MainTheory.Cyclic.chi_add
#print axioms MainTheory.Cyclic.chi_pow
#print axioms MainTheory.Cyclic.chi_eq_one_iff
#print axioms MainTheory.Cyclic.chi_ne_zero
#print axioms MainTheory.Cyclic.chi_injective
#print axioms MainTheory.Cyclic.chi_pow_eq_one_iff
#print axioms MainTheory.Cyclic.addOrderOf_dvd_card
#print axioms MainTheory.Cyclic.isCyclic_of_faithful
#print axioms MainTheory.Cyclic.addOrderOf_orbit21_gap
#print axioms MainTheory.Cyclic.orbit21_projective_order

#print axioms MainTheory.Cyclic.chi_sub
#print axioms MainTheory.RankTwo.normal_form_core
#print axioms MainTheory.RankTwo.addOrderOf_div
#print axioms MainTheory.RankTwo.order_of_two_fiber
#print axioms MainTheory.RankTwo.normal_form_nonvacuous
#print axioms MainTheory.RankTwo.addOrderOf_dvd_q

#print axioms MainTheory.Normalize.primitive_flip
#print axioms MainTheory.RankTwo.gap_ne_zero
#print axioms MainTheory.RankTwo.exists_unit_mul_eq_div

#print axioms MainTheory.Clearing.map_mulVec
#print axioms MainTheory.Clearing.det_smul_eq_adjugate_mulVec
#print axioms MainTheory.Clearing.exists_cleared_of_real
#print axioms MainTheory.Clearing.exists_clearing
#print axioms MainTheory.Clearing.clearing_example

#print axioms MainTheory.Covariance.quad_eq_sum_sq
#print axioms MainTheory.Covariance.quad_eq_zero_iff
#print axioms MainTheory.Covariance.quad_nonneg
#print axioms MainTheory.Covariance.proj_eq_zero_congr
#print axioms MainTheory.Covariance.orthDir_mem_kernel
#print axioms MainTheory.Covariance.along_not_mem_kernel

#print axioms MainTheory.AffineSpan.covariance_eq_of_hasDistance
#print axioms MainTheory.AffineSpan.mean_eq_of_hasDistance

#print axioms MainTheory.D3Bound.dot_eq_of_mulVec_eq
#print axioms MainTheory.D3Bound.exists_rational_agreeing
#print axioms MainTheory.D3Bound.exists_primitive_lift

#print axioms MainTheory.Levels.WImage_orbit21
#print axioms MainTheory.WImages.WImage_orbit9
#print axioms MainTheory.WImages.WImage_orbit10
#print axioms MainTheory.WImages.WImage_orbit11
#print axioms MainTheory.WImages.WImage_orbit16
#print axioms MainTheory.WImages.WImage_orbit22
#print axioms MainTheory.WImages.WImage_orbit23

#print axioms MainTheory.WImages.WImage_orbit7
#print axioms MainTheory.WImages.WImage_orbit8
#print axioms MainTheory.WImages.WImage_orbit45

#print axioms MainTheory.RealGate.exp_eq_of_eigen
#print axioms MainTheory.RealGate.angle_sub_int_of_eigen
#print axioms MainTheory.RealGate.diffMatrix_mulVec
#print axioms MainTheory.RealGate.exists_rational_angle
