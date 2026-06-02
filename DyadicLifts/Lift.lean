import DyadicLifts.Bell
import DyadicLifts.SSResidue

/-!
# The dyadic Bell lift `m ↦ 2m` (definitions, normal form, isometry)

This module formalizes the core of `dyadic_theorem_lean.tex`, Section 3:

* `Definition (Dyadic angle update)` — `aUp`.
* `Definition (High bit modulo 2m)` — `hibit`.
* `Definition (Low/high residue pieces)` — `piece`.
* `Definition (Dyadic lift of codewords)` — `liftVec`.
* `Lemma (Bell normal form of the lift)` — `liftVec_normal`.
* `Lemma (The dyadic lift is an isometry on each sector)` — `liftVec_isom`.

The SS-residue/diagonal action of the lift (`Theorem dyadic-lift-diagonal`) lives
in `DyadicLifts.LiftDiagonal`, which also uses the combinatorial two-value lemma.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- **Dyadic angle update** `a' = (a, m, m)`. -/
def aUp (m : ℕ) (a : Fin n → ℕ) : Fin (n + 2) → ℕ := Fin.append a ![m, m]

/-- **High bit modulo `2m`.** Under the two-value hypothesis, `A_a(s) mod 2m ∈ {b, b+m}`
with `b < m`, so `hibit = true` exactly when `A_a(s) mod 2m ≥ m`, i.e. the carry bit is set. -/
def hibit (m : ℕ) (a : Fin n → ℕ) (s : BitString n) : Bool :=
  decide (m ≤ Asum a s % (2 * m))

/-- **Low/high residue pieces** `ψ^{(h)}`: the part of `ψ` with carry bit `h`. -/
def piece (m : ℕ) (a : Fin n → ℕ) (h : Bool) (ψ : Hil n) : Hil n :=
  fun s => if hibit m a s = h then ψ s else 0

/-- The two pieces reassemble the original vector. -/
lemma piece_add (m : ℕ) (a : Fin n → ℕ) (ψ : Hil n) :
    piece m a false ψ + piece m a true ψ = ψ := by
  funext s
  simp only [piece, Pi.add_apply]
  cases h : hibit m a s <;> simp [h]

/-- **The dyadic Bell lift of a sector-`k` codeword.**
Each basis string `s` is tensored with the Bell flag `Φ_{hibit(s) ⊕ k}`. -/
noncomputable def liftVec (m : ℕ) (a : Fin n → ℕ) (k : Bool) (ψ : Hil n) : Hil (n + 2) :=
  fun w => ψ (bleft w) * bflag (xor (hibit m a (bleft w)) k) (bright w)

/-! ### Linearity -/

lemma liftVec_add (m : ℕ) (a : Fin n → ℕ) (k : Bool) (ψ φ : Hil n) :
    liftVec m a k (ψ + φ) = liftVec m a k ψ + liftVec m a k φ := by
  funext w; simp only [liftVec, Pi.add_apply]; ring

lemma liftVec_smul (m : ℕ) (a : Fin n → ℕ) (k : Bool) (c : ℂ) (ψ : Hil n) :
    liftVec m a k (c • ψ) = c • liftVec m a k ψ := by
  funext w; simp only [liftVec, Pi.smul_apply, smul_eq_mul]; ring

@[simp] lemma liftVec_zero (m : ℕ) (a : Fin n → ℕ) (k : Bool) :
    liftVec m a k (0 : Hil n) = 0 := by
  funext w; simp [liftVec]

/-! ### Bell normal form -/

/-- **Lemma (Bell normal form of the lift).**
`ψ^↑ = ψ^{(0)} ⊗ Φ_k + ψ^{(1)} ⊗ Φ_{¬k}`. For `k = 0` this is
`ψ^{(0)} ⊗ φ + ψ^{(1)} ⊗ ψ`; for `k = 1` it is `ψ^{(0)} ⊗ ψ + ψ^{(1)} ⊗ φ`. -/
lemma liftVec_normal (m : ℕ) (a : Fin n → ℕ) (k : Bool) (ψ : Hil n) :
    liftVec m a k ψ =
      (piece m a false ψ) ⊗ᵥ bflag k + (piece m a true ψ) ⊗ᵥ bflag (!k) := by
  funext w
  simp only [liftVec, tprod, Pi.add_apply, piece]
  cases hk : hibit m a (bleft w) <;> cases k <;> simp [hk]

/-! ### Isometry -/

/-- **Lemma (the dyadic lift is an isometry on each sector).**
`⟨η^↑|ψ^↑⟩ = ⟨η|ψ⟩` for vectors lifted by the same sector rule. -/
lemma liftVec_isom (m : ℕ) (a : Fin n → ℕ) (k : Bool) (η ψ : Hil n) :
    ⟪liftVec m a k η, liftVec m a k ψ⟫ = ⟪η, ψ⟫ := by
  unfold inn liftVec
  rw [sum_split]
  simp only [bleft_append, bright_append]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [show (∑ uv, conj (η s * bflag (xor (hibit m a s) k) uv) *
              (ψ s * bflag (xor (hibit m a s) k) uv))
        = (conj (η s) * ψ s) *
            ∑ uv, conj (bflag (xor (hibit m a s) k) uv) * bflag (xor (hibit m a s) k) uv from ?_]
  · rw [show (∑ uv, conj (bflag (xor (hibit m a s) k) uv) * bflag (xor (hibit m a s) k) uv)
          = inn (bflag (xor (hibit m a s) k)) (bflag (xor (hibit m a s) k)) from rfl,
      inn_bflag, if_pos rfl, mul_one]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro uv _
    rw [map_mul]; ring

/-- A lifted normalized codeword is normalized. -/
lemma liftVec_norm (m : ℕ) (a : Fin n → ℕ) (k : Bool) (ψ : Hil n) (h : ⟪ψ, ψ⟫ = 1) :
    ⟪liftVec m a k ψ, liftVec m a k ψ⟫ = 1 := by
  rw [liftVec_isom, h]

end DyadicLifts
