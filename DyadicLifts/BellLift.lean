import DyadicLifts.Lift
import DyadicLifts.Bell

/-!
# Matrix-element expansion of the dyadic lift

This is the algebraic backbone of the KL propagation: a weight-split Pauli
`E = A ⊗ B` (old block `A`, Bell-pair block `B`) has lifted matrix element equal to
a sum of four products `(old-block carry-piece element) · (Bell-table element)`.

It is pure bilinearity (`mel_add_*`, `mel_append`) together with the Bell normal
form (`liftVec_normal`); it needs no anchor structure and is fully proved.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- **Carry-piece / Bell-table expansion of a lifted matrix element.** -/
lemma liftVec_mel_expand (m : ℕ) (a : Fin n → ℕ) (k₀ k₁ : Bool) (ψ φ : Hil n)
    (A : Fin n → SQ) (B : Fin 2 → SQ) :
    mel (liftVec m a k₀ ψ) (Fin.append A B) (liftVec m a k₁ φ)
      = mel (piece m a false ψ) A (piece m a false φ) * mel (bflag k₀) B (bflag k₁)
      + mel (piece m a false ψ) A (piece m a true φ) * mel (bflag k₀) B (bflag (!k₁))
      + mel (piece m a true ψ) A (piece m a false φ) * mel (bflag (!k₀)) B (bflag k₁)
      + mel (piece m a true ψ) A (piece m a true φ) * mel (bflag (!k₀)) B (bflag (!k₁)) := by
  rw [liftVec_normal, liftVec_normal]
  simp only [mel_add_left, mel_add_right, mel_append]
  ring

end DyadicLifts
