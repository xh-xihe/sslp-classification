import MainTheory.ProjectorCompression
import QECC.PauliKL

/-!
# Frame codes enter the projector-based QECC library

The projector is the same computational-basis matrix, with its rank derived
from orthonormality. Full Pauli KL detection is transported through the existing
small-subsystem tensor theorem; no additional distance assumption is stored.
-/

namespace MainTheory.QECCFrameBridge

open MainTheory.CodeSpec MainTheory.ClassificationLevels
open MainTheory.PauliKernelBTrace
open scoped ComplexOrder

noncomputable section

variable {n K d : ℕ}

theorem projector_rank (F : OrthonormalFrame n K) :
    Matrix.rank (CodeProjector.ofFrame F).kernel = K := by
  rw [projector_eq_frame_mul_conjTranspose,
    Matrix.rank_self_mul_conjTranspose]
  rw [← Matrix.rank_conjTranspose_mul_self (frameMatrix F),
    MainTheory.KLCodeBridge.frameMatrix_gram, Matrix.rank_one]
  simp

/-- The existing frame and the QECC projector encode the same code matrix. -/
def ofFrame (F : OrthonormalFrame n K) : QECC.CodeProjector n K where
  proj := (CodeProjector.ofFrame F).kernel
  hermitian := (CodeProjector.ofFrame F).hermitian
  idempotent := (CodeProjector.ofFrame F).idempotent
  rank_eq := projector_rank F

/-- A phase-free Pauli letter as the existing Fin-2-indexed tensor factor. -/
def letterMatrix (p : QECC.PauliLetter) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => p.entry (i == 1) (j == 1)

theorem letterMatrix_identity : letterMatrix QECC.PauliLetter.I = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem operator_eq_tensorKernel (p : QECC.PauliString n) :
    p.operator = MainTheory.LocalTensorKernel.tensorKernel
      (fun j => letterMatrix (p j)) := by
  ext x y
  apply Finset.prod_congr rfl
  intro j _
  cases x j <;> cases y j <;> simp [letterMatrix, bitIndex]

/-- Full genuine frame KL implies the projector KL definition in QECC. -/
theorem hasDistanceAtLeast (C : ExactCode n K d) :
    (ofFrame C.frame).HasDistanceAtLeast d := by
  intro p hp
  obtain ⟨lam, hlam⟩ := MainTheory.ProjectorCompression.tensor_compression
    C p.support hp (fun j => letterMatrix (p j)) (by
      intro j hj
      have hi : p j = QECC.PauliLetter.I := by
        simpa only [QECC.PauliString.support, Finset.mem_filter,
          Finset.mem_univ, true_and, not_not] using hj
      simpa only [hi] using letterMatrix_identity)
  refine ⟨lam, ?_⟩
  rw [operator_eq_tensorKernel]
  exact hlam

def wordLetter : Fin 4 → QECC.PauliLetter :=
  ![QECC.PauliLetter.I, QECC.PauliLetter.X,
    QECC.PauliLetter.Y, QECC.PauliLetter.Z]

theorem letterMatrix_wordLetter (p : Fin 4) :
    letterMatrix (wordLetter p) = MainTheory.PauliTransferTwo.pauli p := by
  ext i j
  fin_cases p <;> fin_cases i <;> fin_cases j <;>
    simp [wordLetter, letterMatrix, QECC.PauliLetter.entry,
      MainTheory.PauliTransferTwo.pauli]

def ofPauli (p : SS.PauliString n) : QECC.PauliString n :=
  fun j => wordLetter (MainTheory.PauliWordBridge.pauliWordEquiv p j)

theorem ofPauli_weight (p : SS.PauliString n) : (ofPauli p).weight = p.wt := by
  rw [← MainTheory.PauliWordBridge.wordWeight_pauliWordEquiv]
  unfold QECC.PauliString.weight QECC.PauliString.support
    MainTheory.PauliTensorTransfer.wordWeight
  congr 1
  apply Finset.filter_congr
  intro j _
  change wordLetter (MainTheory.PauliWordBridge.pauliWordEquiv p j) ≠
    QECC.PauliLetter.I ↔ MainTheory.PauliWordBridge.pauliWordEquiv p j ≠ 0
  generalize MainTheory.PauliWordBridge.pauliWordEquiv p j = a
  fin_cases a <;> decide

theorem ofPauli_operator (p : SS.PauliString n) :
    (ofPauli p).operator = MainTheory.PauliKernelTrace.pauliKernel p := by
  rw [operator_eq_tensorKernel]
  simp_rw [ofPauli, letterMatrix_wordLetter]
  exact MainTheory.PauliWordBridge.wordKernel_pauliWordEquiv p

/-- The bridge is an equivalence of distance definitions, in both directions. -/
theorem hasDistance_iff (F : OrthonormalFrame n K) (hK : 0 < K) (hd1 : 1 ≤ d) :
    SS.HasDistance F.vec d ↔ (ofFrame F).HasDistanceAtLeast d := by
  constructor
  · intro hd
    exact hasDistanceAtLeast (⟨hK, F, hd⟩ : ExactCode n K d)
  · intro hd p hp
    obtain ⟨lam, hlam⟩ := hd (ofPauli p) (by rw [ofPauli_weight]; omega)
    rw [ofPauli_operator] at hlam
    have hc := (MainTheory.KLCodeBridge.projector_compression_iff F _ lam).1 hlam
    refine ⟨lam, fun i j => ?_⟩
    have hij := congrFun (congrFun hc i) j
    simpa [MainTheory.PauliKernelBTrace.compressed_entry,
      MainTheory.PauliKernelTrace.kernelAction_pauliKernel,
      Matrix.smul_apply, Matrix.one_apply] using hij

end

end MainTheory.QECCFrameBridge
