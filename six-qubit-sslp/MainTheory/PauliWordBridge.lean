import MainTheory.PauliTensorTransfer
import MainTheory.PauliKernelTrace

/-! # The tensor Pauli alphabet agrees with the repository's Pauli matrices -/

namespace MainTheory.PauliWordBridge

open ClassificationLevels LocalTensorKernel PauliTransferTwo PauliTensorTransfer

noncomputable section

variable {n : ℕ}

def label (x z : Bool) : Fin 4 := if x then (if z then 2 else 1) else (if z then 3 else 0)
def xBit : Fin 4 → Bool := ![false, true, true, false]
def zBit : Fin 4 → Bool := ![false, false, true, true]

def pauliWordEquiv : SS.PauliString n ≃ Word n where
  toFun P j := label (P.x j) (P.z j)
  invFun p := ⟨fun j => xBit (p j), fun j => zBit (p j)⟩
  left_inv P := by
    dsimp only
    cases P with
    | mk x z =>
      congr 1 <;> funext j <;> dsimp only <;> cases x j <;> cases z j <;> rfl
  right_inv p := by
    funext j
    change label (xBit (p j)) (zBit (p j)) = p j
    generalize p j = a
    fin_cases a <;> rfl

theorem wordWeight_pauliWordEquiv (P : SS.PauliString n) :
    wordWeight (pauliWordEquiv P) = P.wt := by
  unfold wordWeight SS.PauliString.wt
  congr 1
  apply Finset.filter_congr
  intro j _
  change label (P.x j) (P.z j) ≠ 0 ↔ (P.x j || P.z j) = true
  cases P.x j <;> cases P.z j <;> simp [label]

theorem pauli_entry (px pz x y : Bool) :
    pauli (label px pz) (bitIndex x) (bitIndex y) =
      if y = xor x px then
        (if px && pz then Complex.I else 1) * (if pz && y then (-1 : ℂ) else 1)
      else 0 := by
  cases px <;> cases pz <;> cases x <;> cases y <;> simp [pauli, label, bitIndex]

/-- The matrices really are the physical Pauli operators used by `SS.HasDistance`. -/
theorem wordKernel_pauliWordEquiv (P : SS.PauliString n) :
    wordKernel (pauliWordEquiv P) = PauliKernelTrace.pauliKernel P := by
  classical
  ext x y
  change (∏ j, pauli (label (P.x j) (P.z j)) (bitIndex (x j)) (bitIndex (y j))) = _
  simp_rw [pauli_entry]
  by_cases hxy : y = SS.bxor x P.x
  · have hj (j : Fin n) : y j = xor (x j) (P.x j) := congrFun hxy j
    simp only [hj, if_true]
    rw [Finset.prod_mul_distrib]
    have hI : (∏ j : Fin n, if P.x j && P.z j then Complex.I else 1) = Complex.I ^ P.numY := by
      simp [SS.PauliString.numY, Finset.prod_ite]
    rw [hI]
    have hsign : (∏ j : Fin n, if P.z j && xor (x j) (P.x j) then (-1 : ℂ) else 1) =
        (SS.MacWilliams.chi P.z (SS.bxor x P.x) : ℂ) := by
      simp [SS.MacWilliams.chi, Complex.ofReal_prod, apply_ite]
    rw [hsign]
    simp [PauliKernelTrace.pauliKernel, hxy, SS.MacWilliams.signC_bdot]
  · rw [PauliKernelTrace.pauliKernel, if_neg hxy]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

def operatorA (A : OperatorKernel n) (k : ℕ) : ℝ :=
  ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = k),
    Complex.normSq (Matrix.trace (PauliKernelTrace.pauliKernel P * A))

def wordA (A : OperatorKernel n) (k : ℕ) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p : Word n => wordWeight p = k), Complex.normSq (traces A p)

theorem operatorA_eq_wordA (A : OperatorKernel n) (k : ℕ) : operatorA A k = wordA A k := by
  classical
  simp only [operatorA, wordA, Finset.sum_filter]
  apply Fintype.sum_equiv pauliWordEquiv
  intro P
  simp only [wordWeight_pauliWordEquiv, traces, wordKernel_pauliWordEquiv]

theorem operatorA_ofFrame {K : ℕ} (F : CodeSpec.OrthonormalFrame n K) (k : ℕ) :
    operatorA (CodeProjector.ofFrame F).kernel k = SS.MacWilliams.Aco F.vec k := by
  simp only [operatorA, SS.MacWilliams.Aco, PauliKernelTrace.trace_pauliKernel_mul_projector]

theorem operatorA_tensor_invariant (U : Fin n → Mat2)
    (hU : ∀ j, IsOneQubitUnitary (U j)) (A : OperatorKernel n) (k : ℕ) :
    operatorA (tensorKernel U * A * star (tensorKernel U)) k = operatorA A k := by
  rw [operatorA_eq_wordA, operatorA_eq_wordA]
  exact trace_weight_invariant U hU A k

end

end MainTheory.PauliWordBridge
