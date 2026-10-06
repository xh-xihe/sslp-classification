import MainTheory.GlobalClassificationBridge

/-!
# Unconditional abelianity of the intrinsic diagonal group

The compact-Lie argument in `documents/20260822/main.tex` is needed for
finiteness of the full projective diagonal logical group.  It is not needed
for abelianity.  The physical local phases form a commutative group,
code-preserving phases form a subgroup, and quotienting by projectively
trivial phases preserves commutativity.

This small leaf records that distinction at the actual projector quotient.
It does **not** construct a bounded lift cover, a faithful phase-ratio
character, or an orbit/order audit.
-/

namespace MainTheory.IntrinsicProjectiveAbelian

open MainTheory
open MainTheory.GlobalClassificationBridge

/-- The intrinsic projective diagonal logical group of every exact code is
abelian, without a finiteness, spectral-extraction, or denominator premise. -/
theorem intrinsic_mul_comm {n K d : ℕ}
    (C : CodeSpec.ExactCode n K d) (g h : IntrinsicGroup C) :
    g * h = h * g := by
  exact mul_comm g h

/-- Function-valued form convenient for downstream aggregation theorems. -/
theorem intrinsic_group_abelian {n K d : ℕ}
    (C : CodeSpec.ExactCode n K d) :
    ∀ g h : IntrinsicGroup C, g * h = h * g := by
  intro g h
  exact intrinsic_mul_comm C g h

end MainTheory.IntrinsicProjectiveAbelian
