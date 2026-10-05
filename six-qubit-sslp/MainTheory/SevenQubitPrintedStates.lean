import MainTheory.SevenQubitExampleStates
import MainTheory.SevenQubitPhaseArithmetic

/-! Literal ket coefficients in the manuscript's seven-qubit example. -/
namespace MainTheory.SevenQubitPrintedStates

open MainTheory.SevenQubitExampleData MainTheory.SevenQubitExampleStates
open MainTheory.SevenQubitPhaseArithmetic
open scoped BigOperators
noncomputable section

def coefficient0 (k : Fin 4) : ℝ :=
  ![1 / (Real.sqrt 2 * Real.sqrt 3), 1 / (Real.sqrt 2 * Real.sqrt 3),
    Real.sqrt 2 / (Real.sqrt 2 * Real.sqrt 3),
    Real.sqrt 2 / (Real.sqrt 2 * Real.sqrt 3)] k

def ket (y : SS.BitString 7) : SS.State 7 ℂ := fun x => if x = y then 1 else 0
def printed0 : SS.State 7 ℂ := fun x => ∑ k, (coefficient0 k : ℂ) * ket (point0 k) x
def printed1 : SS.State 7 ℂ := fun x => ∑ k : Fin 6, (1 / Real.sqrt 6 : ℝ) * ket (point1 k) x

theorem point0_injective : Function.Injective point0 := by decide +kernel
theorem point1_injective : Function.Injective point1 := by decide +kernel

theorem probability_point0 : ∀ k : Fin 4,
    probability 0 (point0 k) = ![1/6, 1/6, 1/3, 1/3] k := by decide +kernel
theorem probability_point1 : ∀ k : Fin 6, probability 1 (point1 k) = 1/6 := by decide +kernel

theorem sqrt_six : Real.sqrt (1/6 : ℝ) = 1 / (Real.sqrt 2 * Real.sqrt 3) := by
  rw [show (1/6 : ℝ) = 1 / (2 * 3) from by norm_num,
    Real.sqrt_div (by positivity), Real.sqrt_one, Real.sqrt_mul (by positivity)]

theorem sqrt_three : Real.sqrt (1/3 : ℝ) =
    Real.sqrt 2 / (Real.sqrt 2 * Real.sqrt 3) := by
  rw [Real.sqrt_div (by positivity), Real.sqrt_one]
  field_simp

theorem state0_point (k : Fin 4) : state 0 (point0 k) = (coefficient0 k : ℂ) := by
  change (Real.sqrt (probR 0 (point0 k)) : ℂ) = _
  rw [probR, probability_point0]
  fin_cases k <;> dsimp [coefficient0] <;>
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] <;>
    first | exact congrArg Complex.ofReal sqrt_six | exact congrArg Complex.ofReal sqrt_three

theorem state1_point (k : Fin 6) : state 1 (point1 k) = (1 / Real.sqrt 6 : ℝ) := by
  change (Real.sqrt (probR 1 (point1 k)) : ℂ) = _
  rw [probR, probability_point1]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [Real.sqrt_div (by positivity), Real.sqrt_one]

theorem state0_printed : state 0 = printed0 := by
  classical
  funext x
  by_cases hp : probability 0 x = 0
  · rw [(state_zero 0 x).mpr hp]
    unfold printed0
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k _
    have hx : x ≠ point0 k := by
      intro h
      exact ((support0 x).mpr ⟨k, h⟩) hp
    simp [ket, hx]
  · obtain ⟨k, rfl⟩ := (support0 x).mp hp
    rw [state0_point]
    unfold printed0
    rw [Finset.sum_eq_single k]
    · simp [ket]
    · intro l _ hl
      have hkl : point0 k ≠ point0 l := fun h => hl (point0_injective h).symm
      simp [ket, hkl]
    · simp

theorem state1_printed : state 1 = printed1 := by
  classical
  funext x
  by_cases hp : probability 1 x = 0
  · rw [(state_zero 1 x).mpr hp]
    unfold printed1
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro k _
    have hx : x ≠ point1 k := by
      intro h
      exact ((support1 x).mpr ⟨k, h⟩) hp
    simp [ket, hx]
  · obtain ⟨k, rfl⟩ := (support1 x).mp hp
    rw [state1_point]
    unfold printed1
    rw [Finset.sum_eq_single k]
    · simp [ket]
    · intro l _ hl
      have hkl : point1 k ≠ point1 l := fun h => hl (point1_injective h).symm
      simp [ket, hkl]
    · simp

end
end MainTheory.SevenQubitPrintedStates
