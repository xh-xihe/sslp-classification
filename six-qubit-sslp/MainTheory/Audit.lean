import MainTheory.Rationalize
import MainTheory.Denominator

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
