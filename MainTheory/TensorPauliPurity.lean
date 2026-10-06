import MainTheory.PauliTensorTransfer
import MainTheory.SingletonPurity

/-! # Exact Pauli Parseval for arbitrary finite qubit marginals

This supplies the purity expansion used by the orbit-2 complementary-marginal
argument. The formula holds for an arbitrary complex matrix; Hermiticity is
needed only to replace Frobenius purity by the trace of its square.
-/

namespace MainTheory.TensorPauliPurity

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel
open MainTheory.PauliTransferTwo MainTheory.PauliTensorTransfer
open scoped BigOperators

noncomputable section
variable {n : ℕ}

theorem local_pairing (a b c d : Bool) :
    (∑ p : Fin 4, star (pauli p (bitIndex a) (bitIndex b)) *
      pauli p (bitIndex c) (bitIndex d)) = if a = c ∧ b = d then 2 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    apply Complex.ext <;> norm_num [pauli, bitIndex, Fin.sum_univ_succ]

theorem word_pairing (a b c d : SS.BitString n) :
    (∑ p : Word n, star (wordKernel p a b) * wordKernel p c d) =
      if a = c ∧ b = d then (2 : ℂ) ^ n else 0 := by
  classical
  simp only [wordKernel, tensorKernel, star_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin n) (p : Fin 4) =>
    star (pauli p (bitIndex (a j)) (bitIndex (b j))) *
      pauli p (bitIndex (c j)) (bitIndex (d j)))]
  simp_rw [local_pairing]
  by_cases h : a = c ∧ b = d
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    have hj : ∃ j, ¬ (a j = c j ∧ b j = d j) := by
      by_contra hn
      push_neg at hn
      exact h ⟨funext (fun j => (hn j).1), funext (fun j => (hn j).2)⟩
    obtain ⟨j, hj⟩ := hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem coefficient_pairing (A B : OperatorKernel n) :
    (∑ p : Word n, star (Matrix.trace (wordKernel p * A)) *
      Matrix.trace (wordKernel p * B)) =
      (2 : ℂ) ^ n * ∑ a : SS.BitString n, ∑ b : SS.BitString n,
        star (A b a) * B b a := by
  classical
  have ht (M : OperatorKernel n) (p : Word n) :
      Matrix.trace (wordKernel p * M) =
        ∑ a : SS.BitString n, ∑ b : SS.BitString n, wordKernel p a b * M b a := rfl
  have hexp (p : Word n) :
      star (Matrix.trace (wordKernel p * A)) * Matrix.trace (wordKernel p * B) =
      ∑ a : SS.BitString n, ∑ b : SS.BitString n,
        ∑ c : SS.BitString n, ∑ d : SS.BitString n,
          star (wordKernel p a b) * star (A b a) * (wordKernel p c d * B d c) := by
    rw [ht, ht]
    simp only [star_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [star_mul]
    ring
  simp_rw [hexp]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hs : (∑ p : Word n, ∑ c : SS.BitString n, ∑ d : SS.BitString n,
      star (wordKernel p a b) * star (A b a) * (wordKernel p c d * B d c)) =
      ∑ c : SS.BitString n, ∑ d : SS.BitString n,
        (∑ p : Word n, star (wordKernel p a b) * wordKernel p c d) *
          (star (A b a) * B d c) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hs]
  simp_rw [word_pairing]
  simp [ite_and]

theorem parseval (A : OperatorKernel n) :
    (∑ p : Word n, Complex.normSq (Matrix.trace (wordKernel p * A))) =
      (2 : ℝ) ^ n * MainTheory.SingletonPurity.frobSq A := by
  have hp := coefficient_pairing A A
  simp_rw [SixQubit.CodeEquiv.star_mul_self, ← Complex.ofReal_sum] at hp
  have hh : (∑ p : Word n, Complex.normSq (Matrix.trace (wordKernel p * A))) =
      (2 : ℝ) ^ n * ∑ a : SS.BitString n, ∑ b : SS.BitString n,
        Complex.normSq (A b a) := by exact_mod_cast hp
  rw [Finset.sum_comm] at hh
  exact hh

theorem hermitian_purity (A : OperatorKernel n) (hA : A.conjTranspose = A) :
    (∑ p : Word n, Complex.normSq (Matrix.trace (wordKernel p * A))) =
      (2 : ℝ) ^ n * (Matrix.trace (A * A)).re := by
  have ht := congrArg Complex.re (MainTheory.SingletonPurity.trace_mul_star A)
  rw [hA] at ht
  simp only [Complex.ofReal_re] at ht
  rw [parseval, ← ht]

theorem complementary_pauli_purity {m : ℕ} (M : Matrix (SS.BitString n) (SS.BitString m) ℂ) :
    (∑ p : Word n, Complex.normSq (Matrix.trace (wordKernel p * (M * M.conjTranspose)))) /
        (2 : ℝ) ^ n =
      (∑ p : Word m, Complex.normSq (Matrix.trace (wordKernel p * (M.conjTranspose * M)))) /
        (2 : ℝ) ^ m := by
  rw [parseval, parseval, mul_div_cancel_left₀ _ (by positivity),
    mul_div_cancel_left₀ _ (by positivity)]
  exact MainTheory.SingletonPurity.gram_purity_eq M

end
end MainTheory.TensorPauliPurity
