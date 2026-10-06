import Mathlib
import MainTheory.OuterEnumeration

/-!
# `six:eq:primitiveMobius`, at every value the paper uses

The proposition "Primitive sorted-vector count" of the 20260902 revision
states the closed form

  `P_6(q) = sum_{d | q} mu(d) * (q/d + 5).choose 6`

and then tabulates it at `q = 2, ..., 9` as `six:eq:primitivevalues`.
`PaperReductionChain.primitive_sorted_counts` already carries the eight
tabulated values, obtained by kernel enumeration rather than by the formula.

This file supplies the formula itself at exactly those eight arguments -- every
place the six-qubit reduction uses it -- against Mathlib's genuine
`ArithmeticFunction.moebius`, not a private table.

What is *not* here is the general Mobius inversion.  That needs the counting
identity `(q+5).choose 6 = sum_{d | q} P_6(q/d)`, hence a bijection between
sorted vectors of content `d` and primitive sorted vectors modulo `q/d`; the
module is named for the instance, not for the theorem.
-/

namespace MainTheory.PrimitiveMobius

open ArithmeticFunction

/-! ## The nine Mobius values the eight sums use -/

private theorem sf_two : Squarefree 2 := Nat.prime_two.squarefree
private theorem sf_three : Squarefree 3 := Nat.prime_three.squarefree
private theorem sf_five : Squarefree 5 := (by norm_num : Nat.Prime 5).squarefree
private theorem sf_seven : Squarefree 7 := (by norm_num : Nat.Prime 7).squarefree

private theorem sf_six : Squarefree 6 := by
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h, Nat.squarefree_mul (by norm_num)]
  exact ⟨sf_two, sf_three⟩

private theorem not_sf_four : ¬ Squarefree 4 := by
  intro h
  have := h 2 ⟨1, by norm_num⟩
  rw [Nat.isUnit_iff] at this
  omega

private theorem not_sf_eight : ¬ Squarefree 8 := by
  intro h
  have := h 2 ⟨2, by norm_num⟩
  rw [Nat.isUnit_iff] at this
  omega

private theorem not_sf_nine : ¬ Squarefree 9 := by
  intro h
  have := h 3 ⟨1, by norm_num⟩
  rw [Nat.isUnit_iff] at this
  omega

@[simp] theorem mu_one : (moebius 1 : ℤ) = 1 := by simp

@[simp] theorem mu_two : (moebius 2 : ℤ) = -1 := by
  rw [moebius_apply_of_squarefree sf_two, cardFactors_apply_prime Nat.prime_two]
  norm_num

@[simp] theorem mu_three : (moebius 3 : ℤ) = -1 := by
  rw [moebius_apply_of_squarefree sf_three,
    cardFactors_apply_prime Nat.prime_three]
  norm_num

@[simp] theorem mu_four : (moebius 4 : ℤ) = 0 :=
  moebius_eq_zero_of_not_squarefree not_sf_four

@[simp] theorem mu_five : (moebius 5 : ℤ) = -1 := by
  rw [moebius_apply_of_squarefree sf_five,
    cardFactors_apply_prime (by norm_num : Nat.Prime 5)]
  norm_num

@[simp] theorem mu_six : (moebius 6 : ℤ) = 1 := by
  rw [moebius_apply_of_squarefree sf_six]
  have h : (6 : ℕ) = 2 * 3 := by norm_num
  rw [h, cardFactors_mul (by norm_num) (by norm_num),
    cardFactors_apply_prime Nat.prime_two,
    cardFactors_apply_prime Nat.prime_three]
  norm_num

@[simp] theorem mu_seven : (moebius 7 : ℤ) = -1 := by
  rw [moebius_apply_of_squarefree sf_seven,
    cardFactors_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

@[simp] theorem mu_eight : (moebius 8 : ℤ) = 0 :=
  moebius_eq_zero_of_not_squarefree not_sf_eight

@[simp] theorem mu_nine : (moebius 9 : ℤ) = 0 :=
  moebius_eq_zero_of_not_squarefree not_sf_nine

/-! ## The eight binomial coefficients -/

private theorem ch7 : Nat.choose 7 6 = 7 := by decide
private theorem ch8 : Nat.choose 8 6 = 28 := by decide
private theorem ch9 : Nat.choose 9 6 = 84 := by decide
private theorem ch10 : Nat.choose 10 6 = 210 := by decide
private theorem ch11 : Nat.choose 11 6 = 462 := by decide
private theorem ch12 : Nat.choose 12 6 = 924 := by decide
private theorem ch13 : Nat.choose 13 6 = 1716 := by decide
private theorem ch14 : Nat.choose 14 6 = 3003 := by decide

/-! ## The closed form -/

/-- The right-hand side of `six:eq:primitiveMobius`. -/
def mobiusCount (q : ℕ) : ℤ :=
  ∑ d ∈ q.divisors, (moebius d : ℤ) * ((q / d + 5).choose 6 : ℤ)

private theorem div_two : Nat.divisors 2 = {1, 2} := by decide
private theorem div_three : Nat.divisors 3 = {1, 3} := by decide
private theorem div_four : Nat.divisors 4 = {1, 2, 4} := by decide
private theorem div_five : Nat.divisors 5 = {1, 5} := by decide
private theorem div_six : Nat.divisors 6 = {1, 2, 3, 6} := by decide
private theorem div_seven : Nat.divisors 7 = {1, 7} := by decide
private theorem div_eight : Nat.divisors 8 = {1, 2, 4, 8} := by decide
private theorem div_nine : Nat.divisors 9 = {1, 3, 9} := by decide

theorem mobius_two : mobiusCount 2 = 6 := by
  norm_num [mobiusCount, div_two, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14]

theorem mobius_three : mobiusCount 3 = 27 := by
  norm_num [mobiusCount, div_three, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14]

theorem mobius_four : mobiusCount 4 = 77 := by
  norm_num [mobiusCount, div_four, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14]

theorem mobius_five : mobiusCount 5 = 209 := by
  norm_num [mobiusCount, div_five, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14]

theorem mobius_six : mobiusCount 6 = 428 := by
  norm_num [mobiusCount, div_six, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14]

theorem mobius_seven : mobiusCount 7 = 923 := by
  norm_num [mobiusCount, div_seven, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14]

theorem mobius_eight : mobiusCount 8 = 1632 := by
  norm_num [mobiusCount, div_eight, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14]

theorem mobius_nine : mobiusCount 9 = 2975 := by
  norm_num [mobiusCount, div_nine, ch7, ch8, ch9, ch10, ch11, ch12, ch13, ch14]

/-- **The closed form agrees with the enumeration**, at every modulus the
six-qubit reduction uses.

The left-hand sides are the kernel enumerations behind
`six:eq:primitivevalues`; the right-hand sides are the Mobius sum of
`six:eq:primitiveMobius`. -/
theorem primitiveCount_eq_mobiusCount :
    ((OuterEnumeration.primitiveAngles6 2).length : ℤ) = mobiusCount 2 ∧
      ((OuterEnumeration.primitiveAngles6 3).length : ℤ) = mobiusCount 3 ∧
      ((OuterEnumeration.primitiveAngles6 4).length : ℤ) = mobiusCount 4 ∧
      ((OuterEnumeration.primitiveAngles6 5).length : ℤ) = mobiusCount 5 ∧
      ((OuterEnumeration.primitiveAngles6 6).length : ℤ) = mobiusCount 6 ∧
      ((OuterEnumeration.primitiveAngles6 7).length : ℤ) = mobiusCount 7 ∧
      ((OuterEnumeration.primitiveAngles6 8).length : ℤ) = mobiusCount 8 ∧
      ((OuterEnumeration.primitiveAngles6 9).length : ℤ) = mobiusCount 9 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mobius_two]; norm_num [OuterEnumeration.primitive_two]
  · rw [mobius_three]; norm_num [OuterEnumeration.primitive_three]
  · rw [mobius_four]; norm_num [OuterEnumeration.primitive_four]
  · rw [mobius_five]; norm_num [OuterEnumeration.primitive_five]
  · rw [mobius_six]; norm_num [OuterEnumeration.primitive_six_exact]
  · rw [mobius_seven]; norm_num [OuterEnumeration.primitive_seven_exact]
  · rw [mobius_eight]; norm_num [OuterEnumeration.primitive_eight_exact]
  · rw [mobius_nine]; norm_num [OuterEnumeration.primitive_nine_exact]

end MainTheory.PrimitiveMobius
