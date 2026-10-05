import MainTheory.SevenQubitMinimumOrder
import MainTheory.DiagonalProofSteps
import Mathlib.NumberTheory.Real.Irrational

/-! Actual real phase vectors and the infinite-order representatives. -/
namespace MainTheory.SevenQubitRationalFamily

open MainTheory.SevenQubitExampleData MainTheory.SevenQubitExampleStates
open MainTheory.SevenQubitExampleProjector MainTheory.SevenQubitPhaseArithmetic
open MainTheory.SevenQubitMinimumOrder MainTheory.SevenQubitLogicalCharacter
open scoped BigOperators
open Matrix
noncomputable section

def theta0 : Fin 7 → ℝ := ![1/4, 1/4, 1/4, 1/4, 1/3, 1/3, 1/3]
def theta (t : ℝ) : Fin 7 → ℝ := fun j => theta0 j + t * (direction j : ℝ)
def circleTheta (t : ℝ) : QECC.PhaseVector 7 := fun j => (theta t j : QECC.LocalPhase)

theorem theta_formula (t : ℝ) : theta t = ![1/4+t, 1/4-t, 1/4, 1/4, 1/3+t, 1/3-t, 1/3] := by
  funext j
  fin_cases j <;> norm_num [theta, theta0, direction, sub_eq_add_neg]

theorem circle_quarter : ((1/4 : ℝ) : QECC.LocalPhase) = ZMod.toAddCircle (1 : ZMod 4) := by
  rw [ZMod.toAddCircle_apply, show (1 : ZMod 4).val = 1 from by decide +kernel]
  congr 1
  norm_num

theorem circle_third : ((1/3 : ℝ) : QECC.LocalPhase) = ZMod.toAddCircle (1 : ZMod 3) := by
  rw [ZMod.toAddCircle_apply, show (1 : ZMod 3).val = 1 from by decide +kernel]
  congr 1
  norm_num

theorem theta0_phase : (fun j => (theta0 j : QECC.LocalPhase)) = representative.phase := by
  rw [phase_pattern]
  funext j
  fin_cases j <;> simp only [theta0, pattern, add_zero, sub_zero]
  all_goals first | exact circle_quarter | exact circle_third

theorem family_pattern (t : ℝ) : circleTheta t =
    pattern (ZMod.toAddCircle (1 : ZMod 4)) (ZMod.toAddCircle (1 : ZMod 3))
      (t : QECC.LocalPhase) := by
  have h4 := circle_quarter
  have h3 := circle_third
  simp only [one_div] at h4 h3
  funext j
  fin_cases j <;> simp [circleTheta, theta, theta0, direction, pattern,
    h4, h3, sub_eq_add_neg]

theorem family_preserves (t : ℝ) : projector.Preserves (circleTheta t) := by
  rw [family_pattern]
  apply (preserving_phases _).mpr
  refine ⟨_, _, _, rfl, ?_, ?_⟩
  · rw [← map_nsmul, show 4 • (1 : ZMod 4) = 0 from by decide +kernel, map_zero]
  · rw [← map_nsmul, show 3 • (1 : ZMod 3) = 0 from by decide +kernel, map_zero]

theorem family_class (t : ℝ) :
    projector.projectiveClassMap ⟨circleTheta t, family_preserves t⟩ = targetClass := by
  apply logicalCharacter_injective
  rw [logicalCharacter_class, family_pattern, supportSum_point1, pattern_weights1,
    MainTheory.SevenQubitCharacterArithmetic.circle_character, target_character]
  exact congrArg ZMod.toAddCircle (by decide +kernel :
    MainTheory.SevenQubitCharacterArithmetic.chiFn (1, 1) = 1)

theorem irrational_circle {s : ℝ} (hs : Irrational s) :
    ¬ IsOfFinAddOrder (s : QECC.LocalPhase) := by
  rw [AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div]
  intro q hq
  exact hs.ne_rat q (by simpa using hq.symm)

theorem family_infinite_order {t : ℝ} (ht : Irrational t) :
    orderOf (QECC.diagonalGate (circleTheta t)) = 0 := by
  rw [QECC.diagonalGate_order]
  apply addOrderOf_eq_zero
  intro hf
  have hc : IsOfFinAddOrder ((1/4+t : ℝ) : QECC.LocalPhase) := by
    obtain ⟨k, hk, hkill⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hf
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨k, hk, ?_⟩
    have he := congrFun hkill 0
    simpa [circleTheta, theta, theta0, direction] using he
  have hi : Irrational (1/4+t : ℝ) := by
    simpa using ht.ratCast_add (1/4 : ℚ)
  exact irrational_circle hi hc

theorem direction_identity (u : ℝ) :
    QECC.diagonalGate (fun j => ((u * (direction j : ℝ) : ℝ) : QECC.LocalPhase)) *
      projector.proj = projector.proj := by
  classical
  ext x y
  by_cases hxy : projector.proj x y = 0
  · simp [QECC.diagonalGate, hxy]
  · have hx : probability 0 x ≠ 0 ∨ probability 1 x ≠ 0 := by
      rcases (edges x y).mp hxy with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    have hz : QECC.realSupportWeight (fun j => u * (direction j : ℝ)) x = 0 := by
      rcases hx with h | h
      all_goals
        have hd := direction_zero _ x h
        rw [QECC.realSupportWeight]
        simp only [mul_assoc]
        rw [← Finset.mul_sum]
        have he : (∑ j, (direction j : ℝ) * QECC.bitReal (x j)) = 0 := by
          have he : (∑ j, (direction j : ℝ) * QECC.bitReal (x j)) =
              (weight direction x : ℝ) := by
            simp only [weight, Int.cast_sum]
            apply Finset.sum_congr rfl
            intro j _
            cases x j <;> simp [QECC.bitReal]
          rw [he, hd]
          simp
        rw [he, mul_zero]
    rw [QECC.diagonalGate, Matrix.diagonal_mul,
      QECC.supportPhase_coe_real, hz]
    simp

end
end MainTheory.SevenQubitRationalFamily
