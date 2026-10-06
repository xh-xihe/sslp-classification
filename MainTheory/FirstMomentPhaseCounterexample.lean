import MainTheory.FirstMomentSpanCounterexample
import MainTheory.RealXNormalization

namespace MainTheory.FirstMomentPhaseCounterexample

open MainTheory.PhaseSectorFull MainTheory.RealXNormalization

noncomputable section

def firstSupport : Fin 2 → SS.BitString 2 := ![![false, false], ![true, true]]
def secondSupport : Fin 2 → SS.BitString 2 := ![![true, false], ![false, true]]
def originalAngle : Fin 2 → ℝ := ![1 / 2, 1 / 2]
def replacementAngle : Fin 2 → ℝ := ![1, 0]

theorem first_angles_preserved (i : Fin 2) :
    RealGate.angle replacementAngle (firstSupport i) = RealGate.angle originalAngle (firstSupport i) := by
  fin_cases i <;> norm_num [RealGate.angle, Fin.sum_univ_two,
    replacementAngle, originalAngle, firstSupport]

theorem original_second_angle (i : Fin 2) : RealGate.angle originalAngle (secondSupport i) = 1 / 2 := by
  fin_cases i <;> norm_num [RealGate.angle, Fin.sum_univ_two, originalAngle, secondSupport]

theorem replacement_second_angle_integral (i : Fin 2) :
    ∃ k : ℤ, RealGate.angle replacementAngle (secondSupport i) = (k : ℝ) := by
  fin_cases i
  · exact ⟨1, by norm_num [RealGate.angle, Fin.sum_univ_two, replacementAngle, secondSupport]⟩
  · exact ⟨0, by norm_num [RealGate.angle, Fin.sum_univ_two, replacementAngle, secondSupport]⟩

theorem half_phase_ne_one : phaseExp (1 / 2) ≠ 1 := by
  have he : phaseExp (1 / 2) = -1 := by
    have harg : 2 * (Real.pi : ℂ) * Complex.I * ((1 / 2 : ℝ) : ℂ) =
        (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [phaseExp, harg, Complex.exp_pi_mul_I]
  rw [he]
  norm_num

/-- Even though the first-support physical equations are unchanged, the
second-support logical phase changes. These supports have the equal first
moments proved separately; no KL distance assertion is made for them. -/
theorem relative_phase_can_change (i : Fin 2) :
    phaseExp (RealGate.angle replacementAngle (secondSupport i)) = 1 ∧
      phaseExp (RealGate.angle originalAngle (secondSupport i)) ≠ 1 := by
  obtain ⟨k, hk⟩ := replacement_second_angle_integral i
  constructor
  · exact (FiniteLift.phaseExp_eq_of_sub_int _ 0 k (by simpa using hk)).trans
      (by simp [phaseExp])
  · rw [original_second_angle]
    exact half_phase_ne_one

theorem support_coordinates_match (i j : Fin 2) :
    (if firstSupport i j then (1 : ℝ) else 0) =
      FirstMomentSpanCounterexample.diagonalPoints i j ∧
    (if secondSupport i j then (1 : ℝ) else 0) =
      FirstMomentSpanCounterexample.antiDiagonalPoints i j := by
  fin_cases i <;> fin_cases j <;> exact ⟨rfl, rfl⟩

end

end MainTheory.FirstMomentPhaseCounterexample
