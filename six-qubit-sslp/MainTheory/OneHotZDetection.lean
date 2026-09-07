import MainTheory.OneHotTensorEmbedding
import MainTheory.FiniteTensorDetection
import MainTheory.FrameDistanceOne
import MainTheory.ZDetectionHypothesis

/-! # One-hot codes retain the single-qubit Z detection needed by finite lifts -/

namespace MainTheory.OneHotZDetection

open CodeSpec ClassificationLevels LocalUnitaryKL PauliKernelBTrace PauliKernelTrace
open OneHotTensorEmbedding FiniteTensorKernel FiniteTensorDetection

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] {A : S → Type*}
  [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] {K : ℕ}

set_option linter.unusedSectionVars false

theorem pureZ_kernel {n : ℕ} (k : Fin n) :
    pauliKernel (ZDetection.pureZ k) = Matrix.diagonal (fun x => if x k then (-1 : ℂ) else 1) := by
  classical
  ext x y
  simp only [pauliKernel, ZDetection.pureZ,
    SS.bxor_zero, SixQubit.bdot_stdBasis]
  by_cases hxy : x = y
  · subst y
    simp [SS.signC, SS.PauliString.numY]
  · simp [hxy, Ne.symm hxy]

theorem embedding_pureZ (j : S) (a : A j) :
    (embedding (A := A)).conjTranspose *
      pauliKernel (ZDetection.pureZ (coordinateEquiv (A := A) ⟨j, a⟩)) * embedding (A := A) =
      localKernel j (Matrix.diagonal (fun b => if b = a then (-1 : ℂ) else 1)) := by
  rw [pureZ_kernel, embedding_diagonal, localKernel_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  simp [oneHot_coordinate]

def embeddedFrame (V : Matrix (∀ j, A j) (Fin K) ℂ) (hV : V.conjTranspose * V = 1) :
    OrthonormalFrame (size A) K :=
  frameOfMatrix (embedding (A := A) * V) (by
    calc
      _ = V.conjTranspose * ((embedding (A := A)).conjTranspose * embedding (A := A)) * V := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [embedding_gram]; simpa using hV)

@[simp] theorem frameMatrix_embeddedFrame (V : Matrix (∀ j, A j) (Fin K) ℂ)
    (hV : V.conjTranspose * V = 1) :
    frameMatrix (embeddedFrame V hV) = embedding (A := A) * V := rfl

/-- All operators on one original subsystem are detected, so every `Z` of
its one-hot encoding is detected.  No claim about off-code qubit errors is
smuggled into this implication. -/
theorem zDetects_embeddedFrame (V : Matrix (∀ j, A j) (Fin K) ℂ)
    (hV : V.conjTranspose * V = 1) (hdet : DetectsLocal V) :
    ZDetection.ZDetectsFrame (embeddedFrame V hV) := by
  intro k
  obtain ⟨⟨j, a⟩, rfl⟩ := (coordinateEquiv (A := A)).surjective k
  obtain ⟨c, hc⟩ := hdet j (Matrix.diagonal (fun b => if b = a then (-1 : ℂ) else 1))
  have hcomp : (frameMatrix (embeddedFrame V hV)).conjTranspose *
      pauliKernel (ZDetection.pureZ (coordinateEquiv (A := A) ⟨j, a⟩)) *
        frameMatrix (embeddedFrame V hV) = c • 1 := by
    calc
      _ = V.conjTranspose * ((embedding (A := A)).conjTranspose *
          pauliKernel (ZDetection.pureZ (coordinateEquiv (A := A) ⟨j, a⟩)) * embedding (A := A)) * V := by
        simp [frameMatrix_embeddedFrame, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = c • 1 := by rw [embedding_pureZ, hc]
  simpa only [kernelAction_pauliKernel] using
    (KLTensorSupport.mem_detectedOperators_iff (embeddedFrame V hV) _).1 ⟨c, hcomp⟩

def embeddedCode (V : Matrix (∀ j, A j) (Fin K) ℂ) (hV : V.conjTranspose * V = 1)
    (hK : 0 < K) : ExactCode (size A) K 1 := FrameDistanceOne.codeOfFrame (embeddedFrame V hV) hK

end

end MainTheory.OneHotZDetection
