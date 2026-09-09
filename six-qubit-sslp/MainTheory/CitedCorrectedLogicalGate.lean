import MainTheory.CitedCorrectedFamily

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MainTheory.CitedCorrectedLogicalGate

open MainTheory.ClassificationLevels MainTheory.FiveQubitCorrectedGateSemantics
open SixQubit.Realize

theorem logical_matrix : logical=
    !![(-1+Complex.I)/2,(1+Complex.I)/2;
       (-1+Complex.I)/2,(-1-Complex.I)/2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    norm_num [logical,MainTheory.FiveQubitCorrectedGateData.logical,
      toC,toCre,toCim,rz,SS.rp,z8]

theorem logical_unitary : IsOneQubitUnitary logical := by
  rw [logical_matrix]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    apply Complex.ext <;>
    norm_num [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,
      Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,map_ofNat]

theorem recovered_word (theta : ℝ) (i : Fin 2) :
    MainTheory.CitedAncillaFamily.code theta i=
      fun x => ∑ j,star (logical i j)*
        (MainTheory.LocalTensorKernel.tensorKernel MainTheory.CitedCorrectedFamily.factors).mulVec
          (MainTheory.CitedAncillaFamily.code theta j) x := by
  funext x
  simp_rw [MainTheory.CitedCorrectedFamily.action,Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrow (k : Fin 2) : (∑ j,star (logical i j)*logical k j)=if k=i then 1 else 0 := by
    have hk := congrFun (congrFun logical_unitary.2 k) i
    simpa [Matrix.mul_apply,Matrix.star_apply,Matrix.one_apply,mul_comm,eq_comm] using hk
  simp_rw [← mul_assoc,← Finset.sum_mul,hrow]
  simp

end MainTheory.CitedCorrectedLogicalGate
