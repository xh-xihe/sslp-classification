import MainTheory.SevenQubitRationalFamily
import MainTheory.SevenQubitPrintedStates

/-! Physical gate eigenvectors in the displayed logical basis. -/
namespace MainTheory.SevenQubitLogicalAction

open MainTheory.SevenQubitExampleData MainTheory.SevenQubitExampleStates
open MainTheory.SevenQubitExampleProjector MainTheory.SevenQubitPhaseArithmetic
open MainTheory.SevenQubitRationalFamily
open scoped BigOperators
open Matrix
noncomputable section

theorem state0_eigen (phase : QECC.PhaseVector 7) (hp : projector.Preserves phase) :
    (QECC.diagonalGate phase) *ᵥ state 0 = state 0 := by
  have h0 := ((exact_edges_iff phase).mp hp).1
  funext x
  rw [QECC.diagonalGate, Matrix.mulVec_diagonal]
  by_cases hx : probability 0 x = 0
  · rw [(state_zero 0 x).mpr hx, mul_zero]
  · obtain ⟨k, rfl⟩ := (support0 x).mp hx
    change (((supportSum phase (point0 k)).toCircle : Circle) : ℂ) * _ = _
    rw [supportSum_point0, h0 k]
    simp

theorem state1_eigen (phase : QECC.PhaseVector 7) (hp : projector.Preserves phase) :
    (QECC.diagonalGate phase) *ᵥ state 1 =
      (((supportSum phase (point1 0)).toCircle : Circle) : ℂ) • state 1 := by
  have h1 := ((exact_edges_iff phase).mp hp).2
  funext x
  rw [QECC.diagonalGate, Matrix.mulVec_diagonal]
  change _ = _ * state 1 x
  by_cases hx : probability 1 x = 0
  · rw [(state_zero 1 x).mpr hx, mul_zero, mul_zero]
  · obtain ⟨k, rfl⟩ := (support1 x).mp hx
    change (((supportSum phase (point1 k)).toCircle : Circle) : ℂ) * _ = _
    rw [supportSum_point1, h1 k, ← supportSum_point1]

theorem family_eigenvalues (t : ℝ) :
    (QECC.diagonalGate (circleTheta t)) *ᵥ state 0 = state 0 ∧
      (QECC.diagonalGate (circleTheta t)) *ᵥ state 1 =
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 6) • state 1 := by
  refine ⟨state0_eigen _ (family_preserves t), ?_⟩
  rw [state1_eigen _ (family_preserves t), family_pattern, supportSum_point1,
    pattern_weights1, MainTheory.SevenQubitCharacterArithmetic.circle_character,
    show MainTheory.SevenQubitCharacterArithmetic.chiFn (1, 1) = 1 from by decide +kernel,
    ZMod.toAddCircle_apply, show (1 : ZMod 6).val = 1 from by decide +kernel,
    MainTheory.DiagonalProofSteps.real_circle_exp]
  congr 2
  push_cast
  ring

end
end MainTheory.SevenQubitLogicalAction
