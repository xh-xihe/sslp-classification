import MainTheory.PauliKernelTrace
import SixQubit.BEnumerator

/-!
# The B enumerator as an operator trace

The identity below holds for every complex operator, not only Hermitian
Pauli operators.  It identifies the existing frame-matrix-element definition
with `Tr (E Pi E† Pi)` before applying the paper's `1/K` normalization.
-/

namespace MainTheory.PauliKernelBTrace

open MainTheory.ClassificationLevels MainTheory.CodeSpec
open MainTheory.PauliKernelTrace
open scoped BigOperators ComplexConjugate Matrix

noncomputable section

variable {n K : ℕ}

/-- The columns are the logical frame vectors in the computational basis. -/
def frameMatrix (F : OrthonormalFrame n K) :
    Matrix (SS.BitString n) (Fin K) ℂ := fun x a => F.vec a x

theorem projector_eq_frame_mul_conjTranspose (F : OrthonormalFrame n K) :
    (CodeProjector.ofFrame F).kernel = frameMatrix F * (frameMatrix F)ᴴ := by
  ext x y
  simp [CodeProjector.ofFrame, projectorKernel, frameMatrix, Matrix.mul_apply]

/-- Compressing an operator to the logical frame gives its actual matrix
elements, with the bra in the row index and the ket in the column index. -/
theorem compressed_entry (F : OrthonormalFrame n K) (M : OperatorKernel n)
    (a b : Fin K) :
    ((frameMatrix F)ᴴ * M * frameMatrix F) a b =
      SS.innerC (F.vec a) (kernelAction M (F.vec b)) := by
  classical
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, frameMatrix,
    SS.innerC, kernelAction, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun y _ => by ring

/-- The squared Frobenius norm is a literal matrix trace. -/
theorem trace_mul_conjTranspose (A : Matrix (Fin K) (Fin K) ℂ) :
    Matrix.trace (A * Aᴴ) =
      ((∑ a, ∑ b, Complex.normSq (A a b) : ℝ) : ℂ) := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => Complex.mul_conj _

/-- The paper's B-trace identity for an arbitrary complex physical operator. -/
theorem trace_mul_projector_mul_adjoint_mul_projector
    (F : OrthonormalFrame n K) (M : OperatorKernel n) :
    Matrix.trace
      (M * (CodeProjector.ofFrame F).kernel * Mᴴ *
        (CodeProjector.ofFrame F).kernel) =
      ((∑ a, ∑ b,
        Complex.normSq (SS.innerC (F.vec a) (kernelAction M (F.vec b))) : ℝ) : ℂ) := by
  let V := frameMatrix F
  let A := Vᴴ * M * V
  have htrace : Matrix.trace
      (M * (CodeProjector.ofFrame F).kernel * Mᴴ *
        (CodeProjector.ofFrame F).kernel) = Matrix.trace (A * Aᴴ) := by
    rw [projector_eq_frame_mul_conjTranspose]
    change Matrix.trace (M * (V * Vᴴ) * Mᴴ * (V * Vᴴ)) = _
    calc
      _ = Matrix.trace ((M * V * Vᴴ * Mᴴ * V) * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (Vᴴ * (M * V * Vᴴ * Mᴴ * V)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (A * Aᴴ) := by
        simp only [A, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [htrace, trace_mul_conjTranspose]
  congr 1
  exact Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => by
      rw [show A a b = SS.innerC (F.vec a) (kernelAction M (F.vec b)) from
        compressed_entry F M a b]

/-- Specialization to the actual Pauli matrix defined in `PauliKernelTrace`. -/
theorem trace_pauli_projector_adjoint_projector
    (F : OrthonormalFrame n K) (P : SS.PauliString n) :
    Matrix.trace
      (pauliKernel P * (CodeProjector.ofFrame F).kernel * (pauliKernel P)ᴴ *
        (CodeProjector.ofFrame F).kernel) = (SS.MacWilliams.frob F.vec P : ℂ) := by
  rw [trace_mul_projector_mul_adjoint_mul_projector]
  simp only [kernelAction_pauliKernel, SS.MacWilliams.frob]

/-- The real component is the existing Frobenius coefficient. -/
theorem pauli_trace_re (F : OrthonormalFrame n K) (P : SS.PauliString n) :
    (Matrix.trace
      (pauliKernel P * (CodeProjector.ofFrame F).kernel * (pauliKernel P)ᴴ *
        (CodeProjector.ofFrame F).kernel)).re = SS.MacWilliams.frob F.vec P := by
  rw [trace_pauli_projector_adjoint_projector, Complex.ofReal_re]

theorem pauli_trace_im (F : OrthonormalFrame n K) (P : SS.PauliString n) :
    (Matrix.trace
      (pauliKernel P * (CodeProjector.ofFrame F).kernel * (pauliKernel P)ᴴ *
        (CodeProjector.ofFrame F).kernel)).im = 0 := by
  rw [trace_pauli_projector_adjoint_projector, Complex.ofReal_im]

theorem pauli_trace_nonneg (F : OrthonormalFrame n K) (P : SS.PauliString n) :
    0 ≤ (Matrix.trace
      (pauliKernel P * (CodeProjector.ofFrame F).kernel * (pauliKernel P)ᴴ *
        (CodeProjector.ofFrame F).kernel)).re := by
  rw [pauli_trace_re, SS.MacWilliams.frob]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Complex.normSq_nonneg _

/-- `eq:B-enumerator` with exactly the paper's `1/K` normalization.
The equality is total even for `K = 0`; actual codes have positive rank. -/
theorem BWeight_eq_sum_trace (F : OrthonormalFrame n K) (j : ℕ) :
    BWeight F j =
      (∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j),
        (Matrix.trace
          (pauliKernel P * (CodeProjector.ofFrame F).kernel * (pauliKernel P)ᴴ *
            (CodeProjector.ofFrame F).kernel)).re) / (K : ℝ) := by
  simp only [BWeight, SS.MacWilliams.Bco, pauli_trace_re]
  by_cases hK : (K : ℝ) = 0
  · simp [hK]
  · field_simp

/-- The same normalized formula directly in `ℂ`, with the actual trace and
without a real-part projection. -/
theorem BWeight_cast_eq_sum_trace (F : OrthonormalFrame n K) (j : ℕ) :
    (BWeight F j : ℂ) =
      (∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j),
        Matrix.trace
          (pauliKernel P * (CodeProjector.ofFrame F).kernel * (pauliKernel P)ᴴ *
            (CodeProjector.ofFrame F).kernel)) / (K : ℂ) := by
  rw [BWeight_eq_sum_trace]
  simp only [trace_pauli_projector_adjoint_projector, Complex.ofReal_re,
    Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_natCast]

end

end MainTheory.PauliKernelBTrace
