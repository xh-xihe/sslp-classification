import MainTheory.IntrinsicTransport

/-!
# The intrinsic projective diagonal group is abelian

`thm:finite-projective-group` asserts that the projective diagonal logical
group is finite *abelian*.  Finiteness is established elsewhere; this file
supplies the other half.

There is nothing deep here, but it is not automatic either: `LocalPhase n` is
a pointwise product of copies of `unitary ℂ`, which is commutative, yet
Mathlib registers only `Group` for `unitary`.  So the commutativity has to be
carried by hand from `unitary_mul_comm` up through the symmetry subgroup and
its quotient.
-/

namespace MainTheory.IntrinsicAbelian

open MainTheory.ClassificationLevels
open MainTheory.IntrinsicTransport

variable {n : ℕ}

/-- Diagonal symmetries of a code commute, because their local phases do. -/
theorem symmetryGroup_mul_comm (P : CodeProjector n)
    (u v : diagonalSymmetryGroup P) : u * v = v * u :=
  Subtype.ext (localPhase_mul_comm (u : LocalPhase n) (v : LocalPhase n))

/-- **The intrinsic projective diagonal logical group is abelian.** -/
theorem intrinsicGroup_mul_comm (P : CodeProjector n)
    (g h : IntrinsicProjectiveDiagonalLogicalGroup P) : g * h = h * g := by
  refine QuotientGroup.induction_on g fun u => ?_
  refine QuotientGroup.induction_on h fun v => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    symmetryGroup_mul_comm P u v]

/-- The abelian group structure on the intrinsic group, so that later results
may use `CommGroup` directly instead of rederiving commutativity. -/
instance instCommGroup (P : CodeProjector n) :
    CommGroup (IntrinsicProjectiveDiagonalLogicalGroup P) where
  mul_comm := intrinsicGroup_mul_comm P

/-- The same statement for the group attached to an exact code, which is the
form `thm:finite-projective-group` is stated in. -/
theorem exactCode_intrinsicGroup_mul_comm {K d : ℕ}
    (C : CodeSpec.ExactCode n K d)
    (g h : IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) : g * h = h * g :=
  intrinsicGroup_mul_comm _ g h

end MainTheory.IntrinsicAbelian
