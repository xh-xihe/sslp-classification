import DyadicLifts.LiftDiagonal

/-!
# Iterated dyadic ladders

This module formalizes `dyadic_theorem_lean.tex`, Section 5:

* `Definition (Dyadic ladder data)` — `mr`, `nr`, `ar`.
* `Definition (Rung codewords)` — `psr`.
* `Lemma (Strong sum persists along the ladder)` — `sum_ar`.
* `Theorem (Iterated diagonal action)` — the SS-support invariant `psr_supp{0,1}`
  and the rung-`r` diagonal action `iterated_diagonal_S{0,1}`.

The ladder dimensions are defined by recursion (`nr (r+1) = nr r + 2`,
`mr (r+1) = 2·mr r`) so that the rung codewords live in defeq-correct types.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

/-- Rung modulus `m_r = 2^r m₀`, by recursion. -/
def mr (m0 : ℕ) : ℕ → ℕ
  | 0 => m0
  | r + 1 => 2 * mr m0 r

/-- Rung length `n_r = n₀ + 2r`, by recursion. -/
def nr (n0 : ℕ) : ℕ → ℕ
  | 0 => n0
  | r + 1 => nr n0 r + 2

/-- Rung angle vector `a^{(r)}`, by recursion `a^{(r+1)} = (a^{(r)}, m_r, m_r)`. -/
def ar {n0 : ℕ} (m0 : ℕ) (a0 : Fin n0 → ℕ) : (r : ℕ) → (Fin (nr n0 r) → ℕ)
  | 0 => a0
  | r + 1 => aUp (mr m0 r) (ar m0 a0 r)

/-- Rung codewords `ψ_k^{(r)}`, by iterating the dyadic Bell lift. -/
noncomputable def psr {n0 : ℕ} (m0 : ℕ) (a0 : Fin n0 → ℕ) (ψ : Hil n0) (k : Bool) :
    (r : ℕ) → Hil (nr n0 r)
  | 0 => ψ
  | r + 1 => liftVec (mr m0 r) (ar m0 a0 r) k (psr m0 a0 ψ k r)

/-- `m_r ≥ 1` along the ladder. -/
lemma mr_pos {m0 : ℕ} (hm0 : 1 ≤ m0) (r : ℕ) : 1 ≤ mr m0 r := by
  induction r with
  | zero => exact hm0
  | succ r ih => rw [mr]; omega

/-- `m_r = 2^r m₀`. -/
lemma mr_eq (m0 r : ℕ) : mr m0 r = 2 ^ r * m0 := by
  induction r with
  | zero => simp [mr]
  | succ r ih => rw [mr, ih, pow_succ]; ring

/-- `n_r = n₀ + 2r`. -/
lemma nr_eq (n0 r : ℕ) : nr n0 r = n0 + 2 * r := by
  induction r with
  | zero => simp [nr]
  | succ r ih => rw [nr, ih]; ring

/-- The angle sum over a concatenation. -/
lemma sum_append {p q : ℕ} (a : Fin p → ℕ) (b : Fin q → ℕ) :
    (∑ i, Fin.append a b i) = (∑ i, a i) + ∑ i, b i := by
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl ?_; intro i _; rw [Fin.append_left]
  · refine Finset.sum_congr rfl ?_; intro i _; rw [Fin.append_right]

/-- The angle sum after one dyadic update grows by `2m`. -/
lemma sum_aUp {n : ℕ} (m : ℕ) (a : Fin n → ℕ) :
    (∑ i, aUp m a i) = (∑ i, a i) + 2 * m := by
  have h : (∑ i, aUp m a i) = (∑ i, a i) + ∑ i, (![m, m] : Fin 2 → ℕ) i :=
    sum_append a ![m, m]
  rw [h]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  omega

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ0 ψ1 : Hil n0}

/-- **Lemma (Strong sum persists):** `∑ a^{(r)} = 2 m_r − 1`. -/
lemma sum_ar (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    (∑ i, ar m0 a0 r i) = 2 * mr m0 r - 1 := by
  induction r with
  | zero => simpa [ar, mr] using hss.hsum
  | succ r ih =>
      have hp : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
      have key : (∑ i, ar m0 a0 (r + 1) i) = (∑ i, ar m0 a0 r i) + 2 * mr m0 r :=
        sum_aUp (mr m0 r) (ar m0 a0 r)
      have hmr : mr m0 (r + 1) = 2 * mr m0 r := rfl
      rw [key, ih, hmr]
      omega

/-- The strong-sum total is below `2 m_r`, so the two-value lemma applies at every rung. -/
lemma total_lt_ar (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    (∑ i, ar m0 a0 r i) < 2 * mr m0 r := by
  rw [sum_ar hss r]
  have := mr_pos (m0 := m0) (by have := hss.hm; omega) r
  omega

/-- **SS-support invariant (bottom sector):** every rung-`r` logical-`0` codeword is
supported in `S₀(a^{(r)}; m_r)`. -/
lemma psr_supp0 (hss : StrongSeed n0 m0 a0) (hsupp0 : SuppIn ψ0 (S0 a0 m0)) (r : ℕ) :
    SuppIn (psr m0 a0 ψ0 false r) (S0 (ar m0 a0 r) (mr m0 r)) := by
  induction r with
  | zero => exact hsupp0
  | succ r ih =>
      have hm1 : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
      exact liftVec_S0_residue hm1 (ar m0 a0 r) (total_lt_ar hss r)
        (psr m0 a0 ψ0 false r) ih

/-- **SS-support invariant (top sector).** -/
lemma psr_supp1 (hss : StrongSeed n0 m0 a0) (hsupp1 : SuppIn ψ1 (S1 a0 m0)) (r : ℕ) :
    SuppIn (psr m0 a0 ψ1 true r) (S1 (ar m0 a0 r) (mr m0 r)) := by
  induction r with
  | zero => exact hsupp1
  | succ r ih =>
      have hm1 : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
      exact liftVec_S1_residue hm1 (ar m0 a0 r) (total_lt_ar hss r)
        (psr m0 a0 ψ1 true r) ih

/-- **Theorem (Iterated diagonal action), bottom sector:** `U_{m_r}(a^{(r)})` fixes the
rung-`r` logical-`0` codeword. -/
theorem iterated_diagonal_S0 (hss : StrongSeed n0 m0 a0) (hsupp0 : SuppIn ψ0 (S0 a0 m0))
    (r : ℕ) :
    Udiag (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ0 false r) = psr m0 a0 ψ0 false r := by
  have hp : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
  exact Udiag_S0 (by omega) _ _ (psr_supp0 hss hsupp0 r)

/-- **Theorem (Iterated diagonal action), top sector:** `U_{m_r}(a^{(r)})` scales the
rung-`r` logical-`1` codeword by `e^{-2πi/m_r}`. -/
theorem iterated_diagonal_S1 (hss : StrongSeed n0 m0 a0) (hsupp1 : SuppIn ψ1 (S1 a0 m0))
    (r : ℕ) :
    Udiag (mr m0 r) (ar m0 a0 r) (psr m0 a0 ψ1 true r)
      = Complex.exp (-(2 * Real.pi * Complex.I / ((mr m0 r : ℕ) : ℂ))) • psr m0 a0 ψ1 true r := by
  have hp : 1 ≤ mr m0 r := mr_pos (m0 := m0) (by have := hss.hm; omega) r
  exact Udiag_S1 (by omega) _ _ (psr_supp1 hss hsupp1 r)

end Seed

end DyadicLifts
