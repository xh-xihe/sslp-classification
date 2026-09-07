import MainTheory.SingletonPurity

/-! # The quantum Singleton estimate from two correctable erasure regions -/

namespace MainTheory.SingletonErasureCore

open SingletonPurity

noncomputable section

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C] {K : ℕ}

set_option linter.unusedSectionVars false

def matrixA (F : Fin K → A → B → C → ℂ) : Matrix (Fin K × A) (B × C) ℂ :=
  fun ka bc => F ka.1 ka.2 bc.1 bc.2

def matrixB (F : Fin K → A → B → C → ℂ) : Matrix (Fin K × B) (A × C) ℂ :=
  fun kb ac => F kb.1 ac.1 kb.2 ac.2

/-- Erasure of `A` contains no information about the logical reference. -/
def DecouplesA (F : Fin K → A → B → C → ℂ) (RA : Matrix A A ℂ) : Prop :=
  ∀ k l a a', (∑ b, ∑ c, F k a b c * star (F l a' b c)) = if k = l then RA a a' else 0

def DecouplesB (F : Fin K → A → B → C → ℂ) (RB : Matrix B B ℂ) : Prop :=
  ∀ k l b b', (∑ a, ∑ c, F k a b c * star (F l a b' c)) = if k = l then RB b b' else 0

theorem gramA (F : Fin K → A → B → C → ℂ) (RA : Matrix A A ℂ) (hA : DecouplesA F RA) :
    matrixA F * (matrixA F).conjTranspose = logicalBlock K RA := by
  ext ka la'
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    matrixA, logicalBlock] using hA ka.1 la'.1 ka.2 la'.2

theorem gramB (F : Fin K → A → B → C → ℂ) (RB : Matrix B B ℂ) (hB : DecouplesB F RB) :
    matrixB F * (matrixB F).conjTranspose = logicalBlock K RB := by
  ext kb lb'
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    matrixB, logicalBlock] using hB kb.1 lb'.1 kb.2 lb'.2

theorem partialTrace_gramA (F : Fin K → A → B → C → ℂ) (RB : Matrix B B ℂ)
    (hB : DecouplesB F RB) :
    partialTrace ((matrixA F).conjTranspose * matrixA F) = (K : ℂ) • RB.transpose := by
  ext b b'
  simp only [partialTrace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, matrixA, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  have hlocal (k : Fin K) : (∑ c : C, ∑ a : A, star (F k a b c) * F k a b' c) = RB b' b := by
    rw [Finset.sum_comm]
    simpa only [if_true, mul_comm] using hB k k b' b
  simp only [hlocal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem partialTrace_gramB (F : Fin K → A → B → C → ℂ) (RA : Matrix A A ℂ)
    (hA : DecouplesA F RA) :
    partialTrace ((matrixB F).conjTranspose * matrixB F) = (K : ℂ) • RA.transpose := by
  ext a a'
  simp only [partialTrace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, matrixB, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  have hlocal (k : Fin K) : (∑ c : C, ∑ b : B, star (F k a b c) * F k a' b c) = RA a' a := by
    rw [Finset.sum_comm]
    simpa only [if_true, mul_comm] using hA k k a' a
  simp only [hlocal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem trace_rhoA (F : Fin K → A → B → C → ℂ) (RA : Matrix A A ℂ)
    (hA : DecouplesA F RA) (k : Fin K)
    (hnorm : (∑ a, ∑ b, ∑ c, Complex.normSq (F k a b c)) = 1) : Matrix.trace RA = 1 := by
  calc
    Matrix.trace RA = ∑ a : A, ∑ b : B, ∑ c : C, F k a b c * star (F k a b c) := by
      apply Finset.sum_congr rfl
      intro a _
      simpa only [if_true] using (hA k k a a).symm
    _ = ((∑ a : A, ∑ b : B, ∑ c : C, Complex.normSq (F k a b c) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, mul_comm]
      rfl
    _ = 1 := by rw [hnorm]; norm_num

theorem trace_rhoB (F : Fin K → A → B → C → ℂ) (RB : Matrix B B ℂ)
    (hB : DecouplesB F RB) (k : Fin K)
    (hnorm : (∑ a, ∑ b, ∑ c, Complex.normSq (F k a b c)) = 1) : Matrix.trace RB = 1 := by
  calc
    Matrix.trace RB = ∑ b : B, ∑ a : A, ∑ c : C, F k a b c * star (F k a b c) := by
      apply Finset.sum_congr rfl
      intro b _
      simpa only [if_true] using (hB k k b b).symm
    _ = ((∑ b : B, ∑ a : A, ∑ c : C, Complex.normSq (F k a b c) : ℝ) : ℂ) := by
      simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, mul_comm]
      rfl
    _ = 1 := by rw [Finset.sum_comm, hnorm]; norm_num

/-- **Quantum Singleton for a tripartition.**  If disjoint regions `A` and
`B` each reveal no logical information, the code rank fits in the remaining
system `C`.  The only analytic input is finite Cauchy--Schwarz. -/
theorem rank_le_complement_dimension (F : Fin K → A → B → C → ℂ)
    (hK : 0 < K) (RA : Matrix A A ℂ) (RB : Matrix B B ℂ)
    (hA : DecouplesA F RA) (hB : DecouplesB F RB)
    (hnorm : ∀ k, (∑ a, ∑ b, ∑ c, Complex.normSq (F k a b c)) = 1) :
    K ≤ Fintype.card C := by
  let k : Fin K := ⟨0, hK⟩
  have hRA : RA ≠ 0 := by
    intro h
    have ht := trace_rhoA F RA hA k (hnorm k)
    rw [h, Matrix.trace_zero] at ht
    exact zero_ne_one ht
  have hRB : RB ≠ 0 := by
    intro h
    have ht := trace_rhoB F RB hB k (hnorm k)
    rw [h, Matrix.trace_zero] at ht
    exact zero_ne_one ht
  exact singleton_of_gram_data (matrixA F) (matrixB F) RA RB hRA hRB
    (gramA F RA hA) (gramB F RB hB) (partialTrace_gramA F RB hB) (partialTrace_gramB F RA hA)

end

end MainTheory.SingletonErasureCore
