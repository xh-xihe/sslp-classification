import MainTheory.CoprimePowerRecovery

/-!
# Bounded classes are closed under powers, and under coprime roots

`HasBoundedRepresentation` asks every class of the intrinsic group to be the
class of a symmetry with a bounded label.  This file isolates the purely
group-theoretic half of that obligation.

Two facts are established.  First, the property is closed under powers: the
`d`-th power of a labelled gate still has order at most nine at every site, so
`LabelledGates.exists_label_of_pow_eq_one` renames it.  Second -- and this is
what the entrance actually needs -- if a *coprime power* of `g` has a bounded
representative then so does `g`, because `CoprimePowerRecovery.exists_pow_eq_self`
writes `g` back as a power of that coprime power.

The entrance normalizes the angle vector by a unit of `ZMod q`, so it delivers
a bounded representative of `g ^ c` rather than of `g`.  The second theorem is
exactly the step that removes that discrepancy.
-/

namespace MainTheory.BoundedClassPower

variable {n : ℕ}

open MainTheory.ClassificationLevels
open MainTheory.ProjectiveGroupFinite
open MainTheory.BoundedRepresentation

/-- A class of the intrinsic group is *bounded* when it is the class of a
diagonal symmetry whose local phase is named by a bounded label.  This is the
per-element form of `HasBoundedRepresentation`. -/
def BoundedClass (B : ℕ) (P : CodeProjector n)
    (g : IntrinsicProjectiveDiagonalLogicalGroup P) : Prop :=
  ∃ (lbl : BoundedPhaseLabel n B) (u : diagonalSymmetryGroup P),
    intrinsicClass P u = g ∧ (u : LocalPhase n) = gateOfLabel lbl

/-- Every site of a labelled gate has order dividing the label's modulus. -/
theorem gateOfLabel_pow_eq_one {B : ℕ} (lbl : BoundedPhaseLabel n B) (j : Fin n) :
    ((gateOfLabel lbl j : ℂ)) ^ (lbl.1.val + 1) = 1 := by
  have hq : 0 < lbl.1.val + 1 := Nat.succ_pos _
  have hcast : ((lbl.1.val : ℝ)) + 1 = ((lbl.1.val + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [gateOfLabel, hcast,
    LabelledGates.circlePhase_eq_canonicalRoot_pow _ _ hq, ← pow_mul, mul_comm, pow_mul,
    (LabelledGates.canonicalRoot_isPrimitiveRoot _ hq).pow_eq_one, one_pow]

/-- **Bounded classes are closed under powers.** -/
theorem BoundedClass.pow {B : ℕ} {P : CodeProjector n}
    {g : IntrinsicProjectiveDiagonalLogicalGroup P}
    (h : BoundedClass B P g) (e : ℕ) : BoundedClass B P (g ^ e) := by
  obtain ⟨lbl, u, hclass, hgate⟩ := h
  have hm : lbl.1.val < B := lbl.1.isLt
  have horder : ∀ j, (((u ^ e : diagonalSymmetryGroup P) : LocalPhase n) j : ℂ)
      ^ (lbl.1.val + 1) = 1 := by
    intro j
    have hcoe : (((u ^ e : diagonalSymmetryGroup P) : LocalPhase n) j : ℂ)
        = ((u : LocalPhase n) j : ℂ) ^ e := by
      simp [Pi.pow_apply, SubmonoidClass.coe_pow]
    rw [hcoe, ← pow_mul, mul_comm, pow_mul, hgate, gateOfLabel_pow_eq_one, one_pow]
  obtain ⟨lbl', hlbl'⟩ :=
    LabelledGates.exists_label_of_pow_eq_one lbl.1.val hm _ horder
  refine ⟨lbl', u ^ e, ?_, hlbl'.symm⟩
  rw [← hclass]
  exact QuotientGroup.mk_pow (projectivelyTrivialSubgroup P) u e

/-- **A class with a bounded coprime power is itself bounded.**

If `g ^ k = 1`, `c` is coprime to `k`, and `g ^ c` has a bounded
representative, then so does `g`. -/
theorem BoundedClass.of_pow_coprime {B : ℕ} {P : CodeProjector n}
    {g : IntrinsicProjectiveDiagonalLogicalGroup P} {k c : ℕ}
    (hk : 0 < k) (hgk : g ^ k = 1) (hc : Nat.Coprime c k)
    (h : BoundedClass B P (g ^ c)) : BoundedClass B P g := by
  obtain ⟨d, hd⟩ := CoprimePowerRecovery.exists_pow_eq_self g k hk hgk c hc
  have := h.pow d
  rwa [hd] at this

end MainTheory.BoundedClassPower
