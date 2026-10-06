import MainTheory.SevenQubitExampleData

/-! Support comparisons over any additive commutative group of phases. -/
namespace MainTheory.SevenQubitPhaseArithmetic

open scoped BigOperators
open MainTheory.SevenQubitExampleData
variable {A : Type*} [AddCommGroup A]

def point0 (k : Fin 4) : SS.BitString 7 := nbit (![0, 15, 112, 127] k)
def point1 (k : Fin 6) : SS.BitString 7 := nbit (![51, 60, 101, 105, 86, 90] k)

theorem support0 : ∀ x, probability 0 x ≠ 0 ↔ ∃ k, x = point0 k := by decide +kernel
theorem support1 : ∀ x, probability 1 x ≠ 0 ↔ ∃ k, x = point1 k := by decide +kernel

def supportSum (theta : Fin 7 → A) (x : SS.BitString 7) : A :=
  ∑ j, if x j then theta j else 0

def weights0 (theta : Fin 7 → A) : Fin 4 → A :=
  ![0, theta 0 + theta 1 + theta 2 + theta 3,
    theta 4 + theta 5 + theta 6,
    theta 0 + theta 1 + theta 2 + theta 3 + theta 4 + theta 5 + theta 6]

def weights1 (theta : Fin 7 → A) : Fin 6 → A :=
  ![theta 0 + theta 1 + theta 4 + theta 5,
    theta 2 + theta 3 + theta 4 + theta 5,
    theta 0 + theta 2 + theta 5 + theta 6,
    theta 0 + theta 3 + theta 5 + theta 6,
    theta 1 + theta 2 + theta 4 + theta 6,
    theta 1 + theta 3 + theta 4 + theta 6]

theorem supportSum_point0 (theta : Fin 7 → A) (k : Fin 4) :
    supportSum theta (point0 k) = weights0 theta k := by
  fin_cases k <;> norm_num [supportSum, point0, weights0, nbit, Fin.sum_univ_succ,
    Nat.testBit] <;> (abel_nf; try simp)

theorem supportSum_point1 (theta : Fin 7 → A) (k : Fin 6) :
    supportSum theta (point1 k) = weights1 theta k := by
  fin_cases k <;> norm_num [supportSum, point1, weights1, nbit, Fin.sum_univ_succ,
    Nat.testBit] <;> (abel_nf; try simp)

def pattern (alpha beta u : A) : Fin 7 → A :=
  ![alpha + u, alpha - u, alpha, alpha, beta + u, beta - u, beta]

theorem pattern_weights0 (alpha beta u : A) (k : Fin 4) :
    weights0 (pattern alpha beta u) k = ![0, 4 • alpha, 3 • beta, 4 • alpha + 3 • beta] k := by
  fin_cases k <;> dsimp [weights0, pattern] <;> abel

theorem pattern_weights1 (alpha beta u : A) (k : Fin 6) :
    weights1 (pattern alpha beta u) k = 2 • alpha + 2 • beta := by
  fin_cases k <;> dsimp [weights1, pattern] <;> abel

theorem constant_supports_iff (theta : Fin 7 → A) :
    ((∀ k, weights0 theta k = 0) ∧
      (∀ k, weights1 theta k = weights1 theta 0)) ↔
      ∃ alpha beta u, theta = pattern alpha beta u ∧ 4 • alpha = 0 ∧ 3 • beta = 0 := by
  constructor
  · rintro ⟨h0, h1⟩
    have he23 : (theta 0 + theta 5 + theta 6) + theta 2 =
        (theta 0 + theta 5 + theta 6) + theta 3 := by
      convert (h1 2).trans (h1 3).symm using 1 <;> dsimp [weights1] <;> abel
    have h23 : theta 2 = theta 3 := add_left_cancel he23
    have he01 : (theta 0 + theta 1) + (theta 4 + theta 5) =
        (theta 2 + theta 3) + (theta 4 + theta 5) := by
      convert (h1 1).symm using 1 <;> dsimp [weights1] <;> abel
    have h01 : theta 0 + theta 1 = theta 2 + theta 3 := add_right_cancel he01
    have he14 : (theta 0 + theta 5) + (theta 1 + theta 4) =
        (theta 0 + theta 5) + (theta 2 + theta 6) := by
      convert (h1 2).symm using 1 <;> dsimp [weights1] <;> abel
    have h14 : theta 1 + theta 4 = theta 2 + theta 6 := add_left_cancel he14
    have he05 : (theta 0 + theta 5) + (theta 2 + theta 6) =
        (theta 1 + theta 4) + (theta 2 + theta 6) := by
      convert (h1 2).trans (h1 4).symm using 1 <;> dsimp [weights1] <;> abel
    have h05 : theta 0 + theta 5 = theta 1 + theta 4 := add_right_cancel he05
    have h1eq : theta 1 = theta 2 + theta 2 - theta 0 :=
      (eq_sub_iff_add_eq).mpr (by rw [add_comm, h01, ← h23])
    have h4eq : theta 4 = theta 2 + theta 6 - theta 1 :=
      (eq_sub_iff_add_eq).mpr (by rw [add_comm, h14])
    have h5eq : theta 5 = theta 1 + theta 4 - theta 0 :=
      (eq_sub_iff_add_eq).mpr (by rw [add_comm, h05])
    have hpattern : theta = pattern (theta 2) (theta 6) (theta 0 - theta 2) := by
      funext j
      fin_cases j <;> dsimp [pattern] <;> (try simp only [h1eq, h4eq, h5eq, ← h23]) <;> abel
    refine ⟨theta 2, theta 6, theta 0 - theta 2, hpattern, ?_, ?_⟩
    · have h := h0 1
      rw [hpattern, pattern_weights0] at h
      exact h
    · have h := h0 2
      rw [hpattern, pattern_weights0] at h
      exact h
  · rintro ⟨alpha, beta, u, rfl, ha, hb⟩
    constructor
    · intro k
      rw [pattern_weights0, ha, hb]
      fin_cases k <;> simp
    · intro k
      rw [pattern_weights1, pattern_weights1]

end MainTheory.SevenQubitPhaseArithmetic
