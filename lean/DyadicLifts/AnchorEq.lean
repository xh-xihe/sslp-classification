import DyadicLifts.AnchorRecursion
import DyadicLifts.AnchorCoeff
import DyadicLifts.BellLift
import DyadicLifts.KL

/-!
# Toward anchor-coefficient equality `α_r = β_r`

Helper lemmas (all closed Lean proofs) toward clause (iv) of
`dyadic_theorem_lean.tex`'s Lemma *bell-recursion*: the rung-1 diagonal KL equation
applied to `I^{⊗n₀} ⊗ ZZ` forces `α₀² = β₀²`, and positivity gives `α₀ = β₀`.

This file provides the identity-Pauli infrastructure (`Istr`, `mel_Istr`,
`pauliWt_Istr_ZZ`) and the scaled-ket norm `inn_smul_ket_self`.  The final
`ZZ`-diagonal computation deriving `α₀ = β₀` is carried out in
`DyadicLifts.DistanceTheorem`.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- The all-identity Pauli string. -/
def Istr (n : ℕ) : Fin n → SQ := fun _ => SQ.I

@[simp] lemma pauliWt_Istr : pauliWt (Istr n) = 0 := by
  rw [pauliWt]
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _; simp [Istr]

/-- Matrix element of the identity Pauli. -/
lemma pauliME_Istr (s t : BitString n) :
    pauliME (Istr n) s t = if s = t then 1 else 0 := by
  unfold pauliME Istr
  by_cases h : s = t
  · subst h
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro i _; simp [sqME]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ t i := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [sqME, hi]

/-- The identity Pauli acts trivially. -/
lemma papply_Istr (ψ : Hil n) : papply (Istr n) ψ = ψ := by
  funext s
  rw [papply]
  rw [Finset.sum_eq_single s]
  · rw [pauliME_Istr, if_pos rfl, one_mul]
  · intro t _ ht; rw [pauliME_Istr, if_neg (Ne.symm ht), zero_mul]
  · intro h; exact absurd (Finset.mem_univ s) h

/-- `mel x I y = ⟪x, y⟫`. -/
lemma mel_Istr (x y : Hil n) : mel x (Istr n) y = ⟪x, y⟫ := by
  rw [mel, papply_Istr]

/-- The old-block-identity ⊗ ZZ Pauli has weight `2`. -/
lemma pauliWt_Istr_ZZ : pauliWt (Fin.append (Istr n) ![SQ.Z, SQ.Z]) = 2 := by
  rw [pauliWt_append, pauliWt_Istr]
  decide

/-- Norm of a scaled basis ket: `⟪c • ket s, c • ket s⟫ = conj c * c`. -/
lemma inn_smul_ket_self (c : ℂ) (s : BitString n) :
    ⟪c • ket s, c • ket s⟫ = conj c * c := by
  rw [inn_smul_left, inn_smul_right, inn_ket_ket, if_pos rfl, mul_one]

end DyadicLifts
