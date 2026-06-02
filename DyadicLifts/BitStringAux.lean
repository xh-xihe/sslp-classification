import SS.Pauli
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Bitstring foundations for the dyadic lift

This module formalizes the *finite formalization conventions* of
`dyadic_theorem_lean.tex`, Section 1:

* `Definition (Bitstrings, weight, distance, complement)`
* `Convention (Append and split operations)`

We reuse the bitstring primitives from `SS` (`BitString`, `hammingWt`, `bxor`,
`complement`, `ones`) and add:

* the integer subset sum `Asum a s = ∑ aⱼ sⱼ` (over `ℕ`),
* concatenation of bitstrings/angle vectors via `Fin.append`,
* the basic splitting identities
  `wt (s ++ t) = wt s + wt t`,
  `dist (s ++ u) (t ++ v) = dist s t + dist u v`,
  `complement (s ++ t) = complement s ++ complement t`,
  `Asum (a ++ b) (s ++ t) = Asum a s + Asum b t`.

These are the lemmas used "repeatedly" by the dyadic ladder development.
-/

open scoped BigOperators

namespace DyadicLifts

open SS

variable {n k : ℕ}

/-- `Bit` is a synonym for the `SS` bitstring type, kept for readability. -/
abbrev Bit (n : ℕ) : Type := SS.BitString n

/-- Numerical value of a bit, `0` or `1` (as a natural number). -/
def b2n (b : Bool) : ℕ := if b then 1 else 0

@[simp] lemma b2n_true : b2n true = 1 := rfl
@[simp] lemma b2n_false : b2n false = 0 := rfl

lemma b2n_le_one (b : Bool) : b2n b ≤ 1 := by cases b <;> simp [b2n]

lemma b2n_eq_ite (b : Bool) : b2n b = if b = true then 1 else 0 := by
  cases b <;> rfl

/-- Hamming weight as a sum of bit values. -/
lemma hammingWt_eq_sum (s : BitString n) : hammingWt s = ∑ i, b2n (s i) := by
  rw [hammingWt, Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [b2n_eq_ite]

/-- Hamming weight, written `wt`, matching the `\wt` of the note. -/
abbrev wt (s : BitString n) : ℕ := hammingWt s

/-- Hamming distance `dist s t = wt (s ⊕ t)`. -/
def dist (s t : BitString n) : ℕ := hammingWt (bxor s t)

@[simp] lemma dist_self (s : BitString n) : dist s s = 0 := by
  simp [dist, hammingWt_eq_sum]

lemma dist_comm (s t : BitString n) : dist s t = dist t s := by
  simp [dist, bxor_comm]

/-- Distance to the complement is the complementary weight. -/
lemma dist_complement (s t : BitString n) :
    dist s (complement t) = hammingWt (fun i => !(xor (s i) (t i))) := by
  simp [dist, hammingWt_eq_sum, bxor, complement]

/-- The all-zero bitstring `0ⁿ`. -/
def zeros (n : ℕ) : BitString n := fun _ => false

@[simp] lemma zeros_apply (i : Fin n) : zeros n i = false := rfl

@[simp] lemma hammingWt_zeros : hammingWt (zeros n) = 0 := by
  simp [hammingWt_eq_sum, zeros]

@[simp] lemma hammingWt_ones : hammingWt (ones n) = n := by
  simp [hammingWt_eq_sum, ones]

/-- The integer subset sum `A_a(s) = ∑ⱼ aⱼ sⱼ`, computed in `ℕ`. -/
def Asum (a : Fin n → ℕ) (s : BitString n) : ℕ :=
  ∑ i, a i * b2n (s i)

@[simp] lemma Asum_zeros (a : Fin n → ℕ) : Asum a (zeros n) = 0 := by
  simp [Asum, zeros]

/-- On the all-one string the subset sum is the total `∑ aⱼ`. -/
lemma Asum_ones (a : Fin n → ℕ) : Asum a (ones n) = ∑ i, a i := by
  simp [Asum, ones]

/-- Each term of the subset sum is bounded by the corresponding angle. -/
lemma Asum_le_total (a : Fin n → ℕ) (s : BitString n) : Asum a s ≤ ∑ i, a i := by
  refine Finset.sum_le_sum ?_
  intro i _
  have h : a i * b2n (s i) ≤ a i * 1 := Nat.mul_le_mul (le_refl _) (b2n_le_one _)
  simpa using h

/-! ## Concatenation via `Fin.append` -/

/-- Weight splits over a concatenation. -/
lemma hammingWt_append (s : BitString n) (t : BitString k) :
    hammingWt (Fin.append s t) = hammingWt s + hammingWt t := by
  simp only [hammingWt_eq_sum]
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl ?_; intro i _; rw [Fin.append_left]
  · refine Finset.sum_congr rfl ?_; intro i _; rw [Fin.append_right]

/-- The subset sum splits over a concatenation of angle vector and bitstring. -/
lemma Asum_append (a : Fin n → ℕ) (b : Fin k → ℕ) (s : BitString n) (t : BitString k) :
    Asum (Fin.append a b) (Fin.append s t) = Asum a s + Asum b t := by
  simp only [Asum]
  rw [Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl ?_; intro i _; rw [Fin.append_left, Fin.append_left]
  · refine Finset.sum_congr rfl ?_; intro i _; rw [Fin.append_right, Fin.append_right]

/-- XOR splits over a concatenation. -/
lemma bxor_append (s s' : BitString n) (t t' : BitString k) :
    bxor (Fin.append s t) (Fin.append s' t') = Fin.append (bxor s s') (bxor t t') := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [bxor, Fin.append_left]
  · simp [bxor, Fin.append_right]

/-- Complement splits over a concatenation. -/
lemma complement_append (s : BitString n) (t : BitString k) :
    complement (Fin.append s t) = Fin.append (complement s) (complement t) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [complement, Fin.append_left]
  · simp [complement, Fin.append_right]

/-- Distance splits over a concatenation. -/
lemma dist_append (s s' : BitString n) (t t' : BitString k) :
    dist (Fin.append s t) (Fin.append s' t') = dist s s' + dist t t' := by
  simp [dist, bxor_append, hammingWt_append]

/-- `0ⁿ⁺ᵏ = 0ⁿ ++ 0ᵏ`. -/
lemma zeros_append : (zeros (n + k)) = Fin.append (zeros n) (zeros k) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [zeros, Fin.append_left]
  · simp [zeros, Fin.append_right]

/-- `1ⁿ⁺ᵏ = 1ⁿ ++ 1ᵏ`. -/
lemma ones_append : (ones (n + k)) = Fin.append (ones n) (ones k) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [ones, Fin.append_left]
  · simp [ones, Fin.append_right]

end DyadicLifts
