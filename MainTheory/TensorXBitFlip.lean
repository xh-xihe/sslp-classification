import MainTheory.RealXNormalization
import MainTheory.LocalTensorKernel

namespace MainTheory.TensorXBitFlip

open MainTheory.ClassificationLevels MainTheory.RealXNormalization
open MainTheory.IntrinsicTransport

noncomputable section

variable {n : ℕ}

/-- Literal tensor product of X on the indicated sites and I elsewhere. -/
def tensorX (mask : SS.BitString n) : OperatorKernel n :=
  LocalTensorKernel.tensorKernel (fun j => if mask j then xMatrix else 1)

theorem tensorX_entry (mask x y : SS.BitString n) :
    tensorX mask x y = if x = SS.bxor y mask then 1 else 0 := by
  classical
  have hc (j : Fin n) : (if mask j then xMatrix else (1 : Matrix (Fin 2) (Fin 2) ℂ))
      (bitIndex (x j)) (bitIndex (y j)) =
        if x j = SS.bxor y mask j then 1 else 0 := by
    cases hm : mask j <;> cases hx : x j <;> cases hy : y j <;>
      norm_num [bitIndex, SS.bxor, xMatrix, hm, hx, hy]
  change (∏ j : Fin n, (if mask j then xMatrix else (1 : Matrix (Fin 2) (Fin 2) ℂ))
    (bitIndex (x j)) (bitIndex (y j))) = _
  simp_rw [hc]
  by_cases hxy : x = SS.bxor y mask
  · rw [if_pos hxy]
    apply Finset.prod_eq_one
    intro j _
    rw [congrFun hxy j, if_pos rfl]
  · rw [if_neg hxy]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem kernelAction_tensorX (mask : SS.BitString n) (ψ : SS.State n ℂ) :
    kernelAction (tensorX mask) ψ = fun x => ψ (SS.bxor x mask) := by
  classical
  funext x
  unfold kernelAction
  rw [Finset.sum_eq_single (SS.bxor x mask)]
  · simp only [tensorX_entry, bxor_bxor_self, ↓reduceIte, one_mul]
  · intro y _ hy
    have hn : x ≠ SS.bxor y mask := by
      intro he
      apply hy
      rw [he, bxor_bxor_self]
    rw [tensorX_entry, if_neg hn, zero_mul]
  · simp

theorem tensorX_unitary (mask : SS.BitString n) :
    star (tensorX mask) * tensorX mask = 1 ∧ tensorX mask * star (tensorX mask) = 1 := by
  apply LocalTensorKernel.tensorKernel_unitary
  intro j
  cases mask j
  · simp [IsOneQubitUnitary]
  · simp only [↓reduceIte]
    constructor <;> ext i k <;> fin_cases i <;> fin_cases k <;>
      norm_num [xMatrix, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_two]

end

end MainTheory.TensorXBitFlip
