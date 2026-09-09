import MainTheory.SixQubitExactDistance
import MainTheory.PauliKernelBTrace
import SixQubit.Orbit36Certified

set_option autoImplicit false

namespace MainTheory.SixQubitEnumeratorDisplays

open MainTheory.CodeSpec MainTheory.ClassificationLevels
open SS.MacWilliams

theorem A_trace_definition (F : OrthonormalFrame 6 2) (j : ℕ) :
    AWeight F j = (1/4 : ℝ) *
      ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = j),
        Complex.normSq (Matrix.trace
          (MainTheory.PauliKernelTrace.pauliKernel P * (CodeProjector.ofFrame F).kernel)) := by
  rw [AWeight, MainTheory.PauliKernelTrace.Aco_eq_sum_normSq_trace]
  norm_num
  ring

theorem normal_form (F : OrthonormalFrame 6 2) (hd : SS.HasDistance F.vec 3) :
    (fun j : Fin 7 => AWeight F j) =
      ![1, AWeight F 1, AWeight F 2, AWeight F 3,
        15 - 4*AWeight F 2 - 3*AWeight F 3,
        12 + 3*AWeight F 1 + 4*AWeight F 2 + 3*AWeight F 3,
        4 - 4*AWeight F 1 - AWeight F 2 - AWeight F 3] := by
  have h0 := SixQubit.Pin.Aco_zero F.vec (fun k => by simpa using F.orthonormal k k)
  obtain ⟨h4,h5,h6⟩ := macwilliams_six F.vec hd h0
  simp only [Aco_eq_four_mul_AWeight] at h0 h4 h5 h6
  funext j
  fin_cases j <;> norm_num <;> linarith

theorem orbit36_vectors (F : OrthonormalFrame 6 2)
    (hA : SixQubit.Orbit36Certified.IsOrbit36A F.vec)
    (hB : SixQubit.Orbit36Certified.IsOrbit36B F.vec) :
    (fun j : Fin 7 => AWeight F j) = ![1,0,21/25,0,291/25,384/25,79/25] ∧
    (fun j : Fin 7 => BWeight F j) = ![1,0,21/25,584/25,183/5,984/25,671/25] := by
  rcases hA with ⟨a0,a1,a2,a3,a4,a5,a6⟩
  rcases hB with ⟨b0,b1,b2,b3,b4,b5,b6⟩
  constructor
  · funext j
    fin_cases j <;> norm_num [AWeight,a0,a1,a2,a3,a4,a5,a6]
  · funext j
    fin_cases j <;> norm_num [BWeight,b0,b1,b2,b3,b4,b5,b6]

theorem orbit36_polynomial (F : OrthonormalFrame 6 2)
    (hA : SixQubit.Orbit36Certified.IsOrbit36A F.vec) (z : ℝ) :
    (∑ j : Fin 7, AWeight F j * z ^ j.val) =
      1 + (21/25)*z^2 + (291/25)*z^4 + (384/25)*z^5 + (79/25)*z^6 := by
  have h := (orbit36_vectors F hA
    (SixQubit.Orbit36Certified.orbit36B_of_A F.vec hA)).1
  simp_rw [show ∀ j : Fin 7, AWeight F j =
    (![1,0,21/25,0,291/25,384/25,79/25] : Fin 7 → ℝ) j from fun j => congrFun h j]
  norm_num [Fin.sum_univ_succ]
  ring

end MainTheory.SixQubitEnumeratorDisplays
