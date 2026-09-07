import MainTheory.PauliWordBridge
import MainTheory.MacWilliamsPolynomial

/-! # Genuine local-unitary invariance of the quantum weight enumerators -/

namespace MainTheory.LocalUnitaryEnumerators

open ClassificationLevels LocalTensorKernel PauliTransferTwo PauliTensorTransfer PauliWordBridge

noncomputable section

variable {n K : ℕ}

def permWord (sigma : Equiv.Perm (Fin n)) : Word n ≃ Word n where
  toFun p j := p (sigma j)
  invFun p j := p (sigma.symm j)
  left_inv p := by funext j; simp
  right_inv p := by funext j; simp

theorem wordWeight_permWord (sigma : Equiv.Perm (Fin n)) (p : Word n) :
    wordWeight (permWord sigma p) = wordWeight p := by
  classical
  simp only [wordWeight, Finset.card_filter]
  exact Equiv.sum_comp sigma (fun j => if p j ≠ 0 then 1 else 0)

theorem permutation_conjugate_word (sigma : Equiv.Perm (Fin n)) (q : Word n) :
    star (qubitPermutationKernel sigma) * wordKernel q * qubitPermutationKernel sigma
      = wordKernel (permWord sigma.symm q) := by
  rw [permutationKernel_star, wordKernel, permutationKernel_tensor]
  rw [Matrix.mul_assoc, permutationKernel_mul]
  simp [wordKernel, permWord]

theorem traces_permutation (sigma : Equiv.Perm (Fin n)) (A : OperatorKernel n) (q : Word n) :
    traces (qubitPermutationKernel sigma * A * star (qubitPermutationKernel sigma)) q
      = traces A (permWord sigma.symm q) := by
  unfold traces
  calc Matrix.trace (wordKernel q * (qubitPermutationKernel sigma * A * star (qubitPermutationKernel sigma)))
      = Matrix.trace ((star (qubitPermutationKernel sigma) * wordKernel q * qubitPermutationKernel sigma) * A) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
        simp [Matrix.mul_assoc]
    _ = _ := by rw [permutation_conjugate_word]

theorem wordA_permutation (sigma : Equiv.Perm (Fin n)) (A : OperatorKernel n) (k : ℕ) :
    wordA (qubitPermutationKernel sigma * A * star (qubitPermutationKernel sigma)) k = wordA A k := by
  classical
  simp only [wordA, Finset.sum_filter, traces_permutation]
  apply Fintype.sum_equiv (permWord sigma.symm)
  intro p
  rw [wordWeight_permWord]

/-- The actual operator-trace `A` coefficients are invariant under the full
local-unitary equivalence relation, including qubit permutations. -/
theorem operatorA_luEquivalent {P Q : CodeProjector n} (h : LUEquivalent P Q) (k : ℕ) :
    operatorA Q.kernel k = operatorA P.kernel k := by
  obtain ⟨U, sigma, hU, hQ⟩ := (LocalUnitaryClosure.luEquivalent_iff_tensor P Q).1 h
  have hkernel : Q.kernel = tensorKernel U *
      (qubitPermutationKernel sigma * P.kernel * star (qubitPermutationKernel sigma)) *
      star (tensorKernel U) := by
    rw [hQ]
    simp [localPermutationKernel, star_mul, Matrix.mul_assoc]
  rw [hkernel, operatorA_tensor_invariant U hU, operatorA_eq_wordA, operatorA_eq_wordA]
  exact wordA_permutation sigma P.kernel k

theorem Aco_luEquivalent (F G : CodeSpec.OrthonormalFrame n K)
    (h : LUEquivalent (CodeProjector.ofFrame F) (CodeProjector.ofFrame G)) (k : ℕ) :
    SS.MacWilliams.Aco G.vec k = SS.MacWilliams.Aco F.vec k := by
  rw [← operatorA_ofFrame, ← operatorA_ofFrame]
  exact operatorA_luEquivalent h k

theorem AWeight_luEquivalent (F G : CodeSpec.OrthonormalFrame n K)
    (h : LUEquivalent (CodeProjector.ofFrame F) (CodeProjector.ofFrame G)) (k : ℕ) :
    CodeSpec.AWeight G k = CodeSpec.AWeight F k := by
  simp only [CodeSpec.AWeight, Aco_luEquivalent F G h]

theorem A_polynomial_luEquivalent (F G : CodeSpec.OrthonormalFrame n K)
    (h : LUEquivalent (CodeProjector.ofFrame F) (CodeProjector.ofFrame G)) (x y : ℝ) :
    MacWilliamsPolynomial.A G.vec x y = MacWilliamsPolynomial.A F.vec x y := by
  simp only [MacWilliamsPolynomial.A, MacWilliamsPolynomial.rawA, Aco_luEquivalent F G h]

theorem B_polynomial_luEquivalent (F G : CodeSpec.OrthonormalFrame n K)
    (h : LUEquivalent (CodeProjector.ofFrame F) (CodeProjector.ofFrame G)) (x y : ℝ) :
    MacWilliamsPolynomial.B G.vec x y = MacWilliamsPolynomial.B F.vec x y := by
  rw [MacWilliamsPolynomial.quantum_macwilliams, MacWilliamsPolynomial.quantum_macwilliams,
    A_polynomial_luEquivalent F G h]

private def B_univariate (F : CodeSpec.OrthonormalFrame n K) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n + 1), Polynomial.monomial j (CodeSpec.BWeight F j)

private theorem B_univariate_eval (F : CodeSpec.OrthonormalFrame n K) (y : ℝ) :
    (B_univariate F).eval y = MacWilliamsPolynomial.B F.vec 1 y := by
  rw [MacWilliamsPolynomial.B_eq_sum]
  simp [B_univariate, Polynomial.eval_finset_sum, CodeSpec.BWeight]

private theorem B_univariate_coeff (F : CodeSpec.OrthonormalFrame n K) {k : ℕ} (hk : k ≤ n) :
    (B_univariate F).coeff k = CodeSpec.BWeight F k := by
  classical
  simp [B_univariate, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
    Finset.mem_range, show k < n + 1 by omega]

private theorem BWeight_eq_zero_of_lt (F : CodeSpec.OrthonormalFrame n K) {k : ℕ} (hk : n < k) :
    CodeSpec.BWeight F k = 0 := by
  have hwt (P : SS.PauliString n) : P.wt ≤ n := by
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  have hfilter : Finset.univ.filter (fun P : SS.PauliString n => P.wt = k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro P hP
    have heq := (Finset.mem_filter.1 hP).2
    have := hwt P
    omega
  simp [CodeSpec.BWeight, SS.MacWilliams.Bco, hfilter]

/-- The individual `B` coefficients, with exactly the paper's normalization. -/
theorem BWeight_luEquivalent (F G : CodeSpec.OrthonormalFrame n K)
    (h : LUEquivalent (CodeProjector.ofFrame F) (CodeProjector.ofFrame G)) (k : ℕ) :
    CodeSpec.BWeight G k = CodeSpec.BWeight F k := by
  by_cases hk : k ≤ n
  · have heq : B_univariate G = B_univariate F := by
      apply Polynomial.funext
      intro y
      rw [B_univariate_eval, B_univariate_eval]
      exact B_polynomial_luEquivalent F G h 1 y
    have hc := congrArg (fun p : Polynomial ℝ => p.coeff k) heq
    simpa only [B_univariate_coeff G hk, B_univariate_coeff F hk] using hc
  · rw [BWeight_eq_zero_of_lt G (by omega), BWeight_eq_zero_of_lt F (by omega)]

/-- Both normalized Shor--Laflamme coefficient arrays descend to LU classes. -/
theorem enumerators_luEquivalent (F G : CodeSpec.OrthonormalFrame n K)
    (h : LUEquivalent (CodeProjector.ofFrame F) (CodeProjector.ofFrame G)) :
    (∀ k, CodeSpec.AWeight G k = CodeSpec.AWeight F k) ∧
      ∀ k, CodeSpec.BWeight G k = CodeSpec.BWeight F k :=
  ⟨AWeight_luEquivalent F G h, BWeight_luEquivalent F G h⟩

end

end MainTheory.LocalUnitaryEnumerators
