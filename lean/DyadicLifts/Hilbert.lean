import DyadicLifts.BitStringAux
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The computational Hilbert space `ℋ_n = BitString n → ℂ`

This module formalizes the *computational Hilbert space* of
`dyadic_theorem_lean.tex`, Section 1:

* `Definition (Computational Hilbert space)` — `ℋ_n`, `ket`, `coeff`, `supp`,
  and the inner product `⟨φ|ψ⟩ = ∑ₛ conj(φ s) (ψ s)`.

It also sets up the **tensor split** `ℋ_{n+k} ≃ ℋ_n ⊗ ℋ_k` at the level of
amplitude vectors, which is the workhorse of every dyadic-lift computation:
the inner product factorizes,
`⟨ψ₁ ⊗ χ₁ | ψ₂ ⊗ χ₂⟩ = ⟨ψ₁|ψ₂⟩ · ⟨χ₁|χ₂⟩`.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n k : ℕ}

/-- The computational Hilbert space on `n` qubits: amplitude vectors. -/
abbrev Hil (n : ℕ) : Type := BitString n → ℂ

/-- The computational basis vector `|s⟩` (delta function at `s`). -/
def ket (s : BitString n) : Hil n := fun t => if t = s then 1 else 0

@[simp] lemma ket_apply (s t : BitString n) : ket s t = if t = s then 1 else 0 := rfl

@[simp] lemma ket_self (s : BitString n) : ket s s = 1 := by simp [ket]

/-- The coefficient `⟨s|ψ⟩ = ψ s`. -/
def coeff (ψ : Hil n) (s : BitString n) : ℂ := ψ s

@[simp] lemma coeff_apply (ψ : Hil n) (s : BitString n) : coeff ψ s = ψ s := rfl

/-- The (finite) support of an amplitude vector. -/
noncomputable def supp (ψ : Hil n) : Finset (BitString n) :=
  (Finset.univ : Finset (BitString n)).filter (fun s => ψ s ≠ 0)

@[simp] lemma mem_supp (ψ : Hil n) (s : BitString n) : s ∈ supp ψ ↔ ψ s ≠ 0 := by
  simp [supp]

/-- The Hermitian inner product `⟨φ|ψ⟩ = ∑ₛ conj(φ s) ψ s`. -/
noncomputable def inn (φ ψ : Hil n) : ℂ := ∑ s, conj (φ s) * ψ s

@[inherit_doc] notation "⟪" φ ", " ψ "⟫" => inn φ ψ

/-! ### Linearity of the inner product -/

@[simp] lemma inn_zero_left (ψ : Hil n) : ⟪(0 : Hil n), ψ⟫ = 0 := by
  simp [inn]

@[simp] lemma inn_zero_right (φ : Hil n) : ⟪φ, (0 : Hil n)⟫ = 0 := by
  simp [inn]

lemma inn_add_left (φ₁ φ₂ ψ : Hil n) : ⟪φ₁ + φ₂, ψ⟫ = ⟪φ₁, ψ⟫ + ⟪φ₂, ψ⟫ := by
  simp only [inn, Pi.add_apply, map_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro s _; ring

lemma inn_add_right (φ ψ₁ ψ₂ : Hil n) : ⟪φ, ψ₁ + ψ₂⟫ = ⟪φ, ψ₁⟫ + ⟪φ, ψ₂⟫ := by
  simp only [inn, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro s _; ring

lemma inn_smul_left (c : ℂ) (φ ψ : Hil n) : ⟪c • φ, ψ⟫ = conj c * ⟪φ, ψ⟫ := by
  simp only [inn, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro s _; ring

lemma inn_smul_right (c : ℂ) (φ ψ : Hil n) : ⟪φ, c • ψ⟫ = c * ⟪φ, ψ⟫ := by
  simp only [inn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro s _; ring

lemma inn_sub_left (φ₁ φ₂ ψ : Hil n) : ⟪φ₁ - φ₂, ψ⟫ = ⟪φ₁, ψ⟫ - ⟪φ₂, ψ⟫ := by
  simp only [inn, Pi.sub_apply, map_sub]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro s _; ring

lemma inn_sub_right (φ ψ₁ ψ₂ : Hil n) : ⟪φ, ψ₁ - ψ₂⟫ = ⟪φ, ψ₁⟫ - ⟪φ, ψ₂⟫ := by
  simp only [inn, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro s _; ring

/-- Conjugate symmetry of the inner product. -/
lemma inn_conj (φ ψ : Hil n) : conj (⟪φ, ψ⟫) = ⟪ψ, φ⟫ := by
  simp only [inn, map_sum]
  refine Finset.sum_congr rfl ?_
  intro s _; rw [map_mul, Complex.conj_conj, mul_comm]

/-! ### Inner products with basis vectors -/

@[simp] lemma inn_ket_left (s : BitString n) (ψ : Hil n) : ⟪ket s, ψ⟫ = ψ s := by
  simp only [inn, ket_apply]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht; simp [ht]
  · intro h; exact absurd (Finset.mem_univ s) h

@[simp] lemma inn_ket_right (φ : Hil n) (s : BitString n) : ⟪φ, ket s⟫ = conj (φ s) := by
  simp only [inn, ket_apply]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht; simp [ht]
  · intro h; exact absurd (Finset.mem_univ s) h

lemma inn_ket_ket (s t : BitString n) : ⟪ket s, ket t⟫ = if t = s then 1 else 0 := by
  simp [inn_ket_left]

/-! ## The tensor split `ℋ_{n+k} ≃ ℋ_n ⊗ ℋ_k` -/

/-- Left block of a bitstring on `n+k` qubits. -/
def bleft (w : BitString (n + k)) : BitString n := fun i => w (Fin.castAdd k i)

/-- Right block of a bitstring on `n+k` qubits. -/
def bright (w : BitString (n + k)) : BitString k := fun i => w (Fin.natAdd n i)

@[simp] lemma bleft_append (s : BitString n) (t : BitString k) :
    bleft (Fin.append s t) = s := by
  funext i; simp [bleft, Fin.append_left]

@[simp] lemma bright_append (s : BitString n) (t : BitString k) :
    bright (Fin.append s t) = t := by
  funext i; simp [bright, Fin.append_right]

lemma append_bleft_bright (w : BitString (n + k)) :
    Fin.append (bleft w) (bright w) = w := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- The equivalence `BitString (n+k) ≃ BitString n × BitString k`. -/
def splitEquiv : BitString (n + k) ≃ (BitString n × BitString k) where
  toFun w := (bleft w, bright w)
  invFun p := Fin.append p.1 p.2
  left_inv w := append_bleft_bright w
  right_inv p := by ext <;> simp

/-- Tensor product of amplitude vectors: `(ψ ⊗ χ)(s ++ t) = ψ s · χ t`. -/
def tprod (ψ : Hil n) (χ : Hil k) : Hil (n + k) :=
  fun w => ψ (bleft w) * χ (bright w)

@[inherit_doc] infixr:70 " ⊗ᵥ " => tprod

@[simp] lemma tprod_append (ψ : Hil n) (χ : Hil k) (s : BitString n) (t : BitString k) :
    (ψ ⊗ᵥ χ) (Fin.append s t) = ψ s * χ t := by
  simp [tprod]

lemma tprod_apply (ψ : Hil n) (χ : Hil k) (w : BitString (n + k)) :
    (ψ ⊗ᵥ χ) w = ψ (bleft w) * χ (bright w) := rfl

/-! ### Bilinearity of the tensor product -/

@[simp] lemma tprod_zero_left (χ : Hil k) : (0 : Hil n) ⊗ᵥ χ = 0 := by
  funext w; simp [tprod]

@[simp] lemma tprod_zero_right (ψ : Hil n) : ψ ⊗ᵥ (0 : Hil k) = 0 := by
  funext w; simp [tprod]

lemma tprod_add_left (ψ₁ ψ₂ : Hil n) (χ : Hil k) :
    (ψ₁ + ψ₂) ⊗ᵥ χ = ψ₁ ⊗ᵥ χ + ψ₂ ⊗ᵥ χ := by
  funext w; simp [tprod, add_mul]

lemma tprod_add_right (ψ : Hil n) (χ₁ χ₂ : Hil k) :
    ψ ⊗ᵥ (χ₁ + χ₂) = ψ ⊗ᵥ χ₁ + ψ ⊗ᵥ χ₂ := by
  funext w; simp [tprod, mul_add]

lemma tprod_smul_left (c : ℂ) (ψ : Hil n) (χ : Hil k) :
    (c • ψ) ⊗ᵥ χ = c • (ψ ⊗ᵥ χ) := by
  funext w; simp [tprod, mul_assoc]

lemma tprod_smul_right (c : ℂ) (ψ : Hil n) (χ : Hil k) :
    ψ ⊗ᵥ (c • χ) = c • (ψ ⊗ᵥ χ) := by
  funext w; simp [tprod]; ring

lemma tprod_sub_left (ψ₁ ψ₂ : Hil n) (χ : Hil k) :
    (ψ₁ - ψ₂) ⊗ᵥ χ = ψ₁ ⊗ᵥ χ - ψ₂ ⊗ᵥ χ := by
  funext w; simp [tprod, sub_mul]

/-- `|s⟩ ⊗ |t⟩ = |s ++ t⟩`. -/
lemma tprod_ket (s : BitString n) (t : BitString k) :
    (ket s) ⊗ᵥ (ket t) = ket (Fin.append s t) := by
  funext w
  rw [tprod_apply, ket_apply, ket_apply, ket_apply]
  by_cases h : w = Fin.append s t
  · subst h; simp
  · rw [if_neg h]
    by_cases h1 : bleft w = s <;> by_cases h2 : bright w = t
    · exfalso; apply h; rw [← append_bleft_bright w, h1, h2]
    · simp [h2]
    · simp [h1]
    · simp [h1]

/-! ### The tensor inner-product factorization -/

/-- Sums over `BitString (n+k)` split as double sums over the two blocks. -/
lemma sum_split (F : BitString (n + k) → ℂ) :
    ∑ w : BitString (n + k), F w =
      ∑ s : BitString n, ∑ t : BitString k, F (Fin.append s t) := by
  rw [← Equiv.sum_comp splitEquiv.symm F, Fintype.sum_prod_type]
  rfl

/-- **Tensor inner-product factorization.**
`⟨ψ₁ ⊗ χ₁ | ψ₂ ⊗ χ₂⟩ = ⟨ψ₁|ψ₂⟩ · ⟨χ₁|χ₂⟩`. -/
lemma inn_tprod (ψ₁ ψ₂ : Hil n) (χ₁ χ₂ : Hil k) :
    ⟪ψ₁ ⊗ᵥ χ₁, ψ₂ ⊗ᵥ χ₂⟫ = ⟪ψ₁, ψ₂⟫ * ⟪χ₁, χ₂⟫ := by
  unfold inn
  rw [sum_split, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t _
  simp only [tprod_append, map_mul]
  ring

end DyadicLifts
