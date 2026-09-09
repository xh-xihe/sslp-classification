import MainTheory.PairPartialTrace
import MainTheory.PauliKernelTrace

set_option autoImplicit false

namespace MainTheory.PauliFamilyTrace

open MainTheory.PairPartialTrace MainTheory.PauliKernelTrace

theorem trace_family (code : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) :
    (pauliKernel P*familyKernel code).trace=SS.MacWilliams.trProj code P := by
  classical
  have he (t : SS.BitString 6) : (pauliKernel P*familyKernel code) t t =
      ∑ k : Fin 2,star (code k t)*SS.pauliAct P (code k) t := by
    rw [Matrix.mul_apply,Finset.sum_eq_single (SS.bxor t P.x)]
    · rw [familyKernel,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hb : SS.bdot P.z (SS.bxor t P.x) <;>
        simp [pauliKernel,SS.pauliAct,hb,SS.signC] <;> ring
    · intro y _ hy
      simp [pauliKernel,hy]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  simp only [Matrix.trace,Matrix.diag_apply,he]
  rw [Finset.sum_comm,SS.MacWilliams.trProj]
  apply Finset.sum_congr rfl
  intro k _
  rfl

end MainTheory.PauliFamilyTrace
