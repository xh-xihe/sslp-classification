import DyadicLifts.PauliCoord

/-!
# The Knill–Laflamme conditions for distance `≥ 3`

This module formalizes `dyadic_theorem_lean.tex`, Section 1:

* `Definition (Knill–Laflamme condition for distance at least 3)` — the
  matrix-element predicate `KLmat` and the full predicate `KL`.

We follow the note's convention: `KLmat ψ₀ ψ₁` requires, for every bare Pauli
string `P` of weight `≤ 2`, the vanishing of both off-diagonal matrix elements
and the equality of the two diagonal matrix elements; `KL ψ₀ ψ₁` adds
normalization and orthogonality.  "The code has distance at least `3`" means
`KL ψ₀ ψ₁`.

Normalization `‖ψ‖ = 1` is encoded as `⟪ψ, ψ⟫ = 1`, which is the same condition
since `⟪ψ, ψ⟫ = ∑ |ψ s|²` is real and nonnegative.
-/

open scoped BigOperators

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- The Knill–Laflamme **matrix-element predicate** for weight `≤ 2`:
all weight-`≤2` Paulis have vanishing off-diagonal and equal diagonal
matrix elements on the pair `(ψ₀, ψ₁)`. -/
def KLmat (ψ₀ ψ₁ : Hil n) : Prop :=
  ∀ P : Fin n → SQ, pauliWt P ≤ 2 →
    mel ψ₀ P ψ₁ = 0 ∧ mel ψ₁ P ψ₀ = 0 ∧ mel ψ₀ P ψ₀ = mel ψ₁ P ψ₁

/-- The full Knill–Laflamme predicate for distance `≥ 3`:
normalization, orthogonality, and the matrix-element predicate. -/
def KL (ψ₀ ψ₁ : Hil n) : Prop :=
  ⟪ψ₀, ψ₀⟫ = 1 ∧ ⟪ψ₁, ψ₁⟫ = 1 ∧ ⟪ψ₀, ψ₁⟫ = 0 ∧ KLmat ψ₀ ψ₁

namespace KLmat

/-- Off-diagonal vanishing `⟨ψ₀|P|ψ₁⟩ = 0`. -/
lemma offdiag {ψ₀ ψ₁ : Hil n} (h : KLmat ψ₀ ψ₁) {P : Fin n → SQ}
    (hP : pauliWt P ≤ 2) : mel ψ₀ P ψ₁ = 0 := (h P hP).1

/-- The reverse off-diagonal vanishing `⟨ψ₁|P|ψ₀⟩ = 0`. -/
lemma offdiag' {ψ₀ ψ₁ : Hil n} (h : KLmat ψ₀ ψ₁) {P : Fin n → SQ}
    (hP : pauliWt P ≤ 2) : mel ψ₁ P ψ₀ = 0 := (h P hP).2.1

/-- Diagonal equality `⟨ψ₀|P|ψ₀⟩ = ⟨ψ₁|P|ψ₁⟩`. -/
lemma diag {ψ₀ ψ₁ : Hil n} (h : KLmat ψ₀ ψ₁) {P : Fin n → SQ}
    (hP : pauliWt P ≤ 2) : mel ψ₀ P ψ₀ = mel ψ₁ P ψ₁ := (h P hP).2.2

end KLmat

namespace KL

lemma norm₀ {ψ₀ ψ₁ : Hil n} (h : KL ψ₀ ψ₁) : ⟪ψ₀, ψ₀⟫ = 1 := h.1
lemma norm₁ {ψ₀ ψ₁ : Hil n} (h : KL ψ₀ ψ₁) : ⟪ψ₁, ψ₁⟫ = 1 := h.2.1
lemma ortho {ψ₀ ψ₁ : Hil n} (h : KL ψ₀ ψ₁) : ⟪ψ₀, ψ₁⟫ = 0 := h.2.2.1
lemma mat {ψ₀ ψ₁ : Hil n} (h : KL ψ₀ ψ₁) : KLmat ψ₀ ψ₁ := h.2.2.2

end KL

end DyadicLifts
