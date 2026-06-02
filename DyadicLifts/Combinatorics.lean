import DyadicLifts.SSResidue

/-!
# Combinatorial lemmas for the distance theorem

This module formalizes `dyadic_theorem_lean.tex`, Section 6 (the rung-independent
parts):

* `Lemma (Two-value subset sums when the total sum is below 2m)` — `two_value`.
* `Definition (Strong seed hypotheses)` — `StrongSeed`.
* `Lemma (Strong seed length lower bound)` — `strongSeed_length` (`n > 2`).

The ladder-dependent combinatorial lemmas (`strong-sum-persists`,
`iterated-component-facts`, `no-small-weight`) are proved in `DyadicLifts.Ladder`,
where the iterated angle vector `a^{(r)}` is defined.
-/

open scoped BigOperators

namespace DyadicLifts

open SS

variable {n m : ℕ}

/-- If `A_a(s) < 2m`, then `A_a(s) mod 2m = A_a(s)`. -/
lemma asum_mod_two_m (a : Fin n → ℕ) (htot : (∑ i, a i) < 2 * m) (s : BitString n) :
    Asum a s % (2 * m) = Asum a s :=
  Nat.mod_eq_of_lt (lt_of_le_of_lt (Asum_le_total a s) htot)

/-- **Lemma (Two-value subset sums).**
If the total angle sum is `< 2m` and `A_a(s) ≡ b (mod m)` with `b < m`, then
`A_a(s) ∈ {b, b+m}`. -/
lemma two_value (a : Fin n → ℕ) (b : ℕ) (hb : b < m)
    (htot : (∑ i, a i) < 2 * m) (s : BitString n) (hs : Asum a s % m = b) :
    Asum a s = b ∨ Asum a s = b + m := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le b) hb
  have hlt : Asum a s < 2 * m := lt_of_le_of_lt (Asum_le_total a s) htot
  have hbound : Asum a s / m < 2 := by
    by_contra hcon
    push_neg at hcon
    have h1 : 2 * m ≤ (Asum a s / m) * m := mul_le_mul_right' hcon m
    have h2 : (Asum a s / m) * m ≤ Asum a s := Nat.div_mul_le_self _ _
    omega
  have hdm := Nat.div_add_mod (Asum a s) m
  rw [hs] at hdm
  generalize hgen : Asum a s / m = q at hdm hbound
  interval_cases q <;> omega

/-- The carry bit read off the integer subset sum under the two-value regime:
`A_a(s) = b` (carry `0`) or `A_a(s) = b + m` (carry `1`). -/
lemma asum_eq_of_two_value (a : Fin n → ℕ) (b : ℕ) (hb : b < m)
    (htot : (∑ i, a i) < 2 * m) (s : BitString n) (hs : Asum a s % m = b) :
    (Asum a s = b ∧ ¬ m ≤ Asum a s) ∨ (Asum a s = b + m ∧ m ≤ Asum a s) := by
  rcases two_value a b hb htot s hs with h | h
  · left; exact ⟨h, by omega⟩
  · right; exact ⟨h, by omega⟩

/-- **Lemma (High-bit existence and uniqueness).**
If the total angle sum is `< 2m` and `A_a(s) ≡ b (mod m)` with `b < m`, then the
representative of `A_a(s)` modulo `2m` is either `b` or `b + m`, and these two
residues are distinct.  The dyadic high bit `hibit` records which one occurs;
this lemma is exactly the well-definedness of `Definition (high bit modulo 2m)`. -/
lemma high_bit_exists (a : Fin n → ℕ) (b : ℕ) (hb : b < m)
    (htot : (∑ i, a i) < 2 * m) (s : BitString n) (hs : Asum a s % m = b) :
    (Asum a s % (2 * m) = b ∨ Asum a s % (2 * m) = b + m) ∧ b ≠ b + m := by
  have hmod : Asum a s % (2 * m) = Asum a s := asum_mod_two_m a htot s
  refine ⟨?_, by omega⟩
  rw [hmod]
  exact two_value a b hb htot s hs

/-- **Strong seed hypotheses** (Definition `strong-seed`):
`m ≥ 2`, every angle is `≤ m-2`, and the total angle sum is `2m-1`. -/
structure StrongSeed (n m : ℕ) (a : Fin n → ℕ) : Prop where
  hm : 2 ≤ m
  hbound : ∀ j, a j ≤ m - 2
  hsum : (∑ j, a j) = 2 * m - 1

/-- The strong-sum total is `< 2m`, so the two-value lemma applies. -/
lemma StrongSeed.total_lt {a : Fin n → ℕ} (h : StrongSeed n m a) :
    (∑ j, a j) < 2 * m := by
  rw [h.hsum]; have := h.hm; omega

/-- **Lemma (Strong seed length lower bound):** a strong seed has `n > 2`. -/
lemma strongSeed_length {a : Fin n → ℕ} (h : StrongSeed n m a) : 2 < n := by
  by_contra hn
  push_neg at hn
  have hle : (∑ j, a j) ≤ ∑ _j : Fin n, (m - 2) :=
    Finset.sum_le_sum (fun j _ => h.hbound j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  rw [h.hsum] at hle
  have h2 : n * (m - 2) ≤ 2 * (m - 2) := Nat.mul_le_mul_right _ hn
  have := h.hm
  omega

end DyadicLifts
