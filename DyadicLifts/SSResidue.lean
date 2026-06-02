import DyadicLifts.PauliCoord
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# SS residue codes and the induced transversal diagonal

This module formalizes `dyadic_theorem_lean.tex`, Section 2:

* `Definition (Subset sums and SS support blocks)` — the residue blocks
  `Sres a m b`, `S0 = Sres a m 0`, `S1 = Sres a m (m-1)`.
* `Definition (Two-sector SS codewords)` — `SuppIn`.
* `Lemma (The two SS sectors are disjoint)`.
* `Definition (Transversal diagonal associated with an angle vector)` — `Udiag`,
  defined with the `m`-th root of unity `zeta m = e^{2πi/m}`.
* `Lemma (SS support implies a logical diagonal)` — `Udiag` acts as the scalar
  `zeta m ^ b` on a block-`b` state; for the two sectors the eigenvalues are
  `1` and `zeta m ^ (m-1) = e^{-2πi/m}`.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

/-! ## The `m`-th root of unity -/

/-- The primitive `m`-th root of unity `ζ_m = e^{2πi/m}`. -/
noncomputable def zeta (m : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / m)

lemma zeta_ne_zero (m : ℕ) : zeta m ≠ 0 := Complex.exp_ne_zero _

/-- `ζ_m^m = 1`. -/
lemma zeta_pow_m {m : ℕ} (hm : m ≠ 0) : (zeta m) ^ m = 1 := by
  have hmc : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [zeta, ← Complex.exp_nat_mul]
  have : (m : ℂ) * (2 * Real.pi * Complex.I / m) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [this, Complex.exp_two_pi_mul_I]

/-- `ζ_m^j` depends only on `j mod m`. -/
lemma zeta_pow_mod {m : ℕ} (hm : m ≠ 0) (j : ℕ) : (zeta m) ^ j = (zeta m) ^ (j % m) := by
  conv_lhs => rw [← Nat.div_add_mod j m]
  rw [pow_add, pow_mul, zeta_pow_m hm, one_pow, one_mul]

/-- `ζ_m^(m-1) = ζ_m⁻¹ = e^{-2πi/m}`. -/
lemma zeta_pow_pred {m : ℕ} (hm : m ≠ 0) :
    zeta m ^ (m - 1) = Complex.exp (-(2 * Real.pi * Complex.I / m)) := by
  have key : zeta m ^ (m - 1) * zeta m = 1 := by
    rw [← pow_succ]
    have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hm)
    rw [hm1, zeta_pow_m hm]
  rw [Complex.exp_neg, zeta]
  exact eq_inv_of_mul_eq_one_left key

variable {n : ℕ}

/-! ## SS residue blocks -/

/-- The residue block `S^res_b(a;m) = { s | A_a(s) ≡ b (mod m) }`. -/
def Sres (a : Fin n → ℕ) (m b : ℕ) : Set (BitString n) :=
  { s | Asum a s % m = b % m }

@[simp] lemma mem_Sres (a : Fin n → ℕ) (m b : ℕ) (s : BitString n) :
    s ∈ Sres a m b ↔ Asum a s % m = b % m := Iff.rfl

/-- Bottom sector `S₀ = S^res₀`. -/
def S0 (a : Fin n → ℕ) (m : ℕ) : Set (BitString n) := Sres a m 0

/-- Top sector `S₁ = S^res_{m-1}`. -/
def S1 (a : Fin n → ℕ) (m : ℕ) : Set (BitString n) := Sres a m (m - 1)

@[simp] lemma mem_S0 (a : Fin n → ℕ) (m : ℕ) (s : BitString n) :
    s ∈ S0 a m ↔ Asum a s % m = 0 := by simp [S0]

@[simp] lemma mem_S1 (a : Fin n → ℕ) (m : ℕ) (s : BitString n) :
    s ∈ S1 a m ↔ Asum a s % m = (m - 1) % m := by simp [S1]

/-- `ψ` is supported in `T`: every nonzero amplitude sits at a point of `T`. -/
def SuppIn (ψ : Hil n) (T : Set (BitString n)) : Prop :=
  ∀ s, ψ s ≠ 0 → s ∈ T

/-- **Lemma (the two SS sectors are disjoint).** -/
lemma not_mem_S0_S1 {m : ℕ} (hm : 2 ≤ m) (a : Fin n → ℕ) (s : BitString n)
    (h0 : s ∈ S0 a m) (h1 : s ∈ S1 a m) : False := by
  rw [mem_S0] at h0
  rw [mem_S1] at h1
  rw [h0] at h1
  have hlt : m - 1 < m := by omega
  rw [Nat.mod_eq_of_lt hlt] at h1
  omega

/-- Two-sector SS pairs are automatically orthogonal. -/
lemma inn_eq_zero_of_suppIn {ψ₀ ψ₁ : Hil n} {T₀ T₁ : Set (BitString n)}
    (h0 : SuppIn ψ₀ T₀) (h1 : SuppIn ψ₁ T₁)
    (hd : ∀ s, s ∈ T₀ → s ∈ T₁ → False) : ⟪ψ₀, ψ₁⟫ = 0 := by
  unfold inn
  apply Finset.sum_eq_zero
  intro s _
  by_cases h : ψ₀ s = 0
  · simp [h]
  · by_cases h' : ψ₁ s = 0
    · simp [h']
    · exact (hd s (h0 s h) (h1 s h')).elim

/-- The two SS sectors give orthogonal codewords. -/
lemma ss_pair_ortho {m : ℕ} (hm : 2 ≤ m) {a : Fin n → ℕ} {ψ₀ ψ₁ : Hil n}
    (h0 : SuppIn ψ₀ (S0 a m)) (h1 : SuppIn ψ₁ (S1 a m)) : ⟪ψ₀, ψ₁⟫ = 0 :=
  inn_eq_zero_of_suppIn h0 h1 (not_mem_S0_S1 hm a)

/-! ## The induced transversal diagonal -/

/-- The transversal diagonal `U_m(a)|s⟩ = ζ_m^{A_a(s)}|s⟩`. -/
noncomputable def Udiag (m : ℕ) (a : Fin n → ℕ) (ψ : Hil n) : Hil n :=
  fun s => (zeta m) ^ (Asum a s) * ψ s

/-- **Lemma (SS support implies a logical diagonal).**
If `ψ` is supported in residue block `b`, then `U_m(a)` acts as the scalar
`ζ_m^b`. -/
lemma Udiag_smul_of_suppIn {m : ℕ} (hm : m ≠ 0) (a : Fin n → ℕ) (b : ℕ) (ψ : Hil n)
    (h : SuppIn ψ (Sres a m b)) : Udiag m a ψ = (zeta m ^ b) • ψ := by
  funext s
  by_cases hs : ψ s = 0
  · simp [Udiag, hs]
  · have hb : Asum a s % m = b % m := h s hs
    simp only [Udiag, Pi.smul_apply, smul_eq_mul]
    rw [zeta_pow_mod hm (Asum a s), hb, ← zeta_pow_mod hm b]

/-- Bottom sector: `U_m(a)` fixes a `S₀`-supported state. -/
lemma Udiag_S0 {m : ℕ} (hm : m ≠ 0) (a : Fin n → ℕ) (ψ : Hil n)
    (h : SuppIn ψ (S0 a m)) : Udiag m a ψ = ψ := by
  rw [Udiag_smul_of_suppIn hm a 0 ψ h]
  simp

/-- Top sector: `U_m(a)` scales an `S₁`-supported state by `ζ_m^(m-1) = e^{-2πi/m}`. -/
lemma Udiag_S1 {m : ℕ} (hm : m ≠ 0) (a : Fin n → ℕ) (ψ : Hil n)
    (h : SuppIn ψ (S1 a m)) :
    Udiag m a ψ = (Complex.exp (-(2 * Real.pi * Complex.I / m))) • ψ := by
  rw [Udiag_smul_of_suppIn hm a (m - 1) ψ h, zeta_pow_pred hm]

end DyadicLifts
