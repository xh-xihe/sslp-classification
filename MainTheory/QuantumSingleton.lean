import MainTheory.SingletonTripartition

/-! # The quantum Singleton bound from the genuine Knill--Laflamme predicate

The nontrivial-rank hypothesis is necessary for the manuscript's distance
convention: a rank-one frame detects every error, for every claimed distance.
For `K ≥ 2`, the theorem proves that the exponent is nonnegative as well as
the bound itself, so natural subtraction cannot hide this condition.
-/

namespace MainTheory.QuantumSingleton

open SingletonTripartition PauliKernelBTrace

noncomputable section

variable {n K d a b c : ℕ}

theorem frame_rank_le (F : CodeSpec.OrthonormalFrame n K) : K ≤ 2 ^ n := by
  classical
  have hgram : (frameMatrix F).conjTranspose * frameMatrix F = 1 := by
    ext k l
    simpa only [frameMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using F.orthonormal k l
  have h := (Matrix.rank_mul_le_left (frameMatrix F).conjTranspose (frameMatrix F)).trans
    (Matrix.rank_le_card_width (frameMatrix F).conjTranspose)
  simpa only [hgram, Matrix.rank_one, Fintype.card_fin, SS.BitString,
    Fintype.card_fun, Fintype.card_bool] using h

/-- The block theorem with an explicit length identity, convenient for
arithmetic choices of the two erased regions. -/
theorem rank_le_pow_of_partition (Q : CodeSpec.ExactCode n K d)
    (h : n = a + (b + c)) (ha : a < d) (hb : b < d) : K ≤ 2 ^ c := by
  subst n
  exact rank_le_pow_complement Q ha hb

/-- A nontrivial quantum code cannot have two erasure regions, each smaller
than the distance, covering all its physical qubits. -/
theorem twice_distance_sub_one_le_length (Q : CodeSpec.ExactCode n K d) (hK : 2 ≤ K) :
    2 * (d - 1) ≤ n := by
  by_contra h
  have hd : 0 < d := by omega
  let a := min n (d - 1)
  let b := n - a
  have ha : a < d := by dsimp [a]; omega
  have hb : b < d := by dsimp [a, b]; omega
  have heq : n = a + (b + 0) := by dsimp [a, b]; omega
  have hbound := rank_le_pow_of_partition Q heq ha hb
  norm_num at hbound
  omega

/-- **Quantum Singleton bound.**  This is the paper's `K ≤ 2^(n−2(d−1))`
for arbitrary code length, rank and distance, with the necessary `K ≥ 2`
qualification.  Both the KL-to-erasure step and the dimension estimate are
proved in the kernel; no entropy or recovery theorem is assumed. -/
theorem quantum_singleton (Q : CodeSpec.ExactCode n K d) (hK : 2 ≤ K) :
    2 * (d - 1) ≤ n ∧ K ≤ 2 ^ (n - 2 * (d - 1)) := by
  have hsize := twice_distance_sub_one_le_length Q hK
  refine ⟨hsize, ?_⟩
  by_cases hd : d = 0
  · simpa [hd] using frame_rank_le Q.frame
  · exact rank_le_pow_of_partition Q (a := d - 1) (b := d - 1)
      (c := n - 2 * (d - 1)) (by omega) (by omega) (by omega)

theorem twice_distance_le_length_add_one (Q : CodeSpec.ExactCode n K d) (hK : 2 ≤ K) :
    2 * d ≤ n + 1 := by
  obtain ⟨hsize, hbound⟩ := quantum_singleton Q hK
  have hpos : 0 < n - 2 * (d - 1) := by
    by_contra h
    have heq : n - 2 * (d - 1) = 0 := by omega
    rw [heq] at hbound
    norm_num at hbound
    omega
  omega

/-- The six-qubit, one-logical-qubit distance limit used in the paper. -/
theorem six_qubit_distance_le_three (Q : CodeSpec.ExactCode 6 2 d) : d ≤ 3 := by
  have h := twice_distance_le_length_add_one Q (by decide)
  omega

end

end MainTheory.QuantumSingleton
