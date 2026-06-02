import DyadicLifts.Hilbert

/-!
# Bare Pauli strings via their coordinate action

This module formalizes `dyadic_theorem_lean.tex`, Section 1:

* `Definition (Bare Pauli strings and their weight)` — a bare `n`-qubit Pauli is
  a function `Fin n → SQ` into the four single-qubit Paulis `{I,X,Y,Z}`.
* `Remark (Lean representation of Pauli strings)` — we use the **coordinate
  action**: the matrix element `⟨s|P|t⟩` is the product of single-qubit matrix
  elements, and `papply P ψ` is the action on an amplitude vector.
* `Lemma (Basis-transition support of a Pauli string)` — a nonzero matrix
  element forces `dist s t ≤ wt P`.

We also prove the **tensor factorizations** that drive the whole development:
`⟨s++u|A⊗B|t++v⟩ = ⟨s|A|t⟩·⟨u|B|v⟩`, `wt (A⊗B) = wt A + wt B`, and
`papply (A⊗B) (ψ⊗χ) = (papply A ψ) ⊗ (papply B χ)`.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

/-- The four single-qubit Pauli matrices. -/
inductive SQ where
  | I : SQ
  | X : SQ
  | Y : SQ
  | Z : SQ
deriving DecidableEq, Fintype, Repr

/-- Single-qubit Pauli matrix element `⟨s|P|t⟩` (row `s`, column `t`). -/
def sqME : SQ → Bool → Bool → ℂ
  | SQ.I, s, t => if s = t then 1 else 0
  | SQ.X, s, t => if s = t then 0 else 1
  | SQ.Z, s, t => if s = t then (if t then -1 else 1) else 0
  | SQ.Y, s, t => if s = t then 0 else (if t then -Complex.I else Complex.I)

@[simp] lemma sqME_I (s t : Bool) : sqME SQ.I s t = if s = t then 1 else 0 := rfl
@[simp] lemma sqME_X (s t : Bool) : sqME SQ.X s t = if s = t then 0 else 1 := rfl
@[simp] lemma sqME_Z (s t : Bool) :
    sqME SQ.Z s t = if s = t then (if t then -1 else 1) else 0 := rfl
@[simp] lemma sqME_Y (s t : Bool) :
    sqME SQ.Y s t = if s = t then 0 else (if t then -Complex.I else Complex.I) := rfl

variable {n k : ℕ}

/-- The matrix element `⟨s|P|t⟩` of a bare Pauli string, by coordinatewise product. -/
def pauliME (P : Fin n → SQ) (s t : BitString n) : ℂ :=
  ∏ i, sqME (P i) (s i) (t i)

/-- Pauli weight: number of non-identity tensor factors. -/
def pauliWt (P : Fin n → SQ) : ℕ :=
  (Finset.univ.filter (fun i => P i ≠ SQ.I)).card

/-- Pauli weight as a sum of indicators. -/
lemma pauliWt_eq_sum (P : Fin n → SQ) :
    pauliWt P = ∑ i, (if P i ≠ SQ.I then 1 else 0) := by
  rw [pauliWt, Finset.card_filter]

/-- The action of a bare Pauli string on an amplitude vector. -/
noncomputable def papply (P : Fin n → SQ) (ψ : Hil n) : Hil n :=
  fun s => ∑ t, pauliME P s t * ψ t

/-- The Knill–Laflamme matrix element `⟨ψ₀|P|ψ₁⟩`. -/
noncomputable def mel (ψ₀ : Hil n) (P : Fin n → SQ) (ψ₁ : Hil n) : ℂ :=
  ⟪ψ₀, papply P ψ₁⟫

/-! ### Linearity of `papply` and `mel` -/

lemma papply_add (P : Fin n → SQ) (ψ φ : Hil n) :
    papply P (ψ + φ) = papply P ψ + papply P φ := by
  funext s
  simp only [papply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro t _; ring

lemma papply_smul (P : Fin n → SQ) (c : ℂ) (ψ : Hil n) :
    papply P (c • ψ) = c • papply P ψ := by
  funext s
  simp only [papply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t _; ring

lemma papply_sub (P : Fin n → SQ) (ψ φ : Hil n) :
    papply P (ψ - φ) = papply P ψ - papply P φ := by
  funext s
  simp only [papply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro t _; ring

@[simp] lemma papply_zero (P : Fin n → SQ) : papply P (0 : Hil n) = 0 := by
  funext s; simp [papply]

lemma mel_add_right (ψ₀ : Hil n) (P : Fin n → SQ) (ψ φ : Hil n) :
    mel ψ₀ P (ψ + φ) = mel ψ₀ P ψ + mel ψ₀ P φ := by
  simp only [mel, papply_add, inn_add_right]

lemma mel_add_left (ψ φ : Hil n) (P : Fin n → SQ) (ψ₁ : Hil n) :
    mel (ψ + φ) P ψ₁ = mel ψ P ψ₁ + mel φ P ψ₁ := by
  simp only [mel, inn_add_left]

lemma mel_smul_right (ψ₀ : Hil n) (P : Fin n → SQ) (c : ℂ) (ψ : Hil n) :
    mel ψ₀ P (c • ψ) = c * mel ψ₀ P ψ := by
  simp only [mel, papply_smul, inn_smul_right]

lemma mel_smul_left (c : ℂ) (ψ₀ : Hil n) (P : Fin n → SQ) (ψ : Hil n) :
    mel (c • ψ₀) P ψ = conj c * mel ψ₀ P ψ := by
  simp only [mel, inn_smul_left]

lemma mel_sub_right (ψ₀ : Hil n) (P : Fin n → SQ) (ψ φ : Hil n) :
    mel ψ₀ P (ψ - φ) = mel ψ₀ P ψ - mel ψ₀ P φ := by
  simp only [mel, papply_sub, inn_sub_right]

lemma mel_sub_left (ψ φ : Hil n) (P : Fin n → SQ) (ψ₁ : Hil n) :
    mel (ψ - φ) P ψ₁ = mel ψ P ψ₁ - mel φ P ψ₁ := by
  simp only [mel, inn_sub_left]

@[simp] lemma mel_zero_right (ψ₀ : Hil n) (P : Fin n → SQ) :
    mel ψ₀ P (0 : Hil n) = 0 := by simp [mel]

@[simp] lemma mel_zero_left (P : Fin n → SQ) (ψ₁ : Hil n) :
    mel (0 : Hil n) P ψ₁ = 0 := by simp [mel]

/-- `⟨ψ₀|P|s⟩ = conj(ψ₀ acting...)`; matrix element against a basis ket on the right. -/
lemma mel_ket_right (ψ₀ : Hil n) (P : Fin n → SQ) (t : BitString n) :
    mel ψ₀ P (ket t) = ∑ s, conj (ψ₀ s) * pauliME P s t := by
  simp only [mel, inn, papply]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [Finset.sum_eq_single t]
  · simp
  · intro u _ hu; simp [ket_apply, hu]
  · intro h; exact absurd (Finset.mem_univ t) h

/-! ### Tensor / concatenation factorizations -/

/-- Pauli weight splits over a concatenation. -/
lemma pauliWt_append (A : Fin n → SQ) (B : Fin k → SQ) :
    pauliWt (Fin.append A B) = pauliWt A + pauliWt B := by
  simp only [pauliWt_eq_sum]
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl ?_; intro i _; rw [Fin.append_left]
  · refine Finset.sum_congr rfl ?_; intro i _; rw [Fin.append_right]

/-- General factorization of a concatenated Pauli matrix element. -/
lemma pauliME_append_general (A : Fin n → SQ) (B : Fin k → SQ) (w z : BitString (n + k)) :
    pauliME (Fin.append A B) w z =
      pauliME A (bleft w) (bleft z) * pauliME B (bright w) (bright z) := by
  unfold pauliME
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl ?_; intro i _; rw [Fin.append_left]; rfl
  · refine Finset.prod_congr rfl ?_; intro i _; rw [Fin.append_right]; rfl

/-- Matrix element of a tensor Pauli on tensor basis vectors. -/
lemma pauliME_append (A : Fin n → SQ) (B : Fin k → SQ)
    (s : BitString n) (u : BitString k) (t : BitString n) (v : BitString k) :
    pauliME (Fin.append A B) (Fin.append s u) (Fin.append t v) =
      pauliME A s t * pauliME B u v := by
  rw [pauliME_append_general]; simp

/-- **Operator tensor factorization** of the Pauli action. -/
lemma papply_append (A : Fin n → SQ) (B : Fin k → SQ) (ψ : Hil n) (χ : Hil k) :
    papply (Fin.append A B) (ψ ⊗ᵥ χ) = (papply A ψ) ⊗ᵥ (papply B χ) := by
  funext w
  unfold papply tprod
  rw [sum_split, Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro v _
  rw [pauliME_append_general]
  simp only [bleft_append, bright_append]
  ring

/-- **Matrix-element tensor factorization.**
`⟨ψ₀⊗χ₀ | A⊗B | ψ₁⊗χ₁⟩ = ⟨ψ₀|A|ψ₁⟩ · ⟨χ₀|B|χ₁⟩`. -/
lemma mel_append (A : Fin n → SQ) (B : Fin k → SQ)
    (ψ₀ ψ₁ : Hil n) (χ₀ χ₁ : Hil k) :
    mel (ψ₀ ⊗ᵥ χ₀) (Fin.append A B) (ψ₁ ⊗ᵥ χ₁) = mel ψ₀ A ψ₁ * mel χ₀ B χ₁ := by
  simp only [mel, papply_append, inn_tprod]

/-! ### Basis-transition support -/

/-- **Lemma (Basis-transition support of a Pauli string).**
If `⟨s|P|t⟩ ≠ 0`, then `s` and `t` differ only on `X`/`Y` qubits; in particular
`dist s t ≤ wt P`. -/
lemma dist_le_pauliWt {P : Fin n → SQ} {s t : BitString n}
    (h : pauliME P s t ≠ 0) : dist s t ≤ pauliWt P := by
  have hfac : ∀ i, sqME (P i) (s i) (t i) ≠ 0 := by
    intro i h0
    exact h (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  unfold dist hammingWt pauliWt
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bxor_apply] at hi ⊢
  intro hPI
  have hne : s i ≠ t i := by cases hs : s i <;> cases ht : t i <;> simp_all
  have hf := hfac i
  rw [hPI] at hf
  exact hf (by simp [hne])

/-- Companion fact: at qubits where `P` is `I` or `Z`, a nonzero element forces equal bits. -/
lemma eq_of_diag_pauliME {P : Fin n → SQ} {s t : BitString n}
    (h : pauliME P s t ≠ 0) (i : Fin n) (hP : P i = SQ.I ∨ P i = SQ.Z) :
    s i = t i := by
  have hf : sqME (P i) (s i) (t i) ≠ 0 := by
    intro h0
    exact h (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  by_contra hne
  rcases hP with hP | hP <;> rw [hP] at hf <;> exact hf (by simp [hne])

end DyadicLifts
