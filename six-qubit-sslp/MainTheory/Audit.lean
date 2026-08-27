import MainTheory.Rationalize
import MainTheory.Denominator
import MainTheory.Gate
import MainTheory.PhaseSector
import MainTheory.Normalize

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
