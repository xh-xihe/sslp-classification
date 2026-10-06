import MainTheory.CompletionCodeBridge
import MainTheory.LocalUnitaryKL
import MainTheory.Orbit3ScalarCategoryRealization

/-! # Arbitrary spectator U(2) preserves actual orbit-3 completions

The transformed states enter the same normalized distance-three completion
type. This supplies generator preservation for the spectator Hadamard and
phase gates in the cubic averaging argument.
-/

namespace MainTheory.Orbit3SpectatorUnitary

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.CubeCompletionTransport
open MainTheory.DirectoryEnumeratorImages MainTheory.ClassificationLevels
open MainTheory.LocalTensorKernel MainTheory.PauliTransferTwo MainTheory.LocalUnitaryKL

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

theorem fiber_update_zero : ∀ k : Fin 2, ∀ s : SS.BitString 6, ∀ b : Bool,
    Function.update s 0 b ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) ↔
      s ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) := by
  decide +kernel

theorem fiber_spectator_invariant (k : Fin 2) (s t : SS.BitString 6)
    (h : ∀ j, j ≠ 0 → s j = t j) :
    s ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) ↔
      t ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) := by
  have ht : t = Function.update s 0 (t 0) := by
    funext j
    by_cases hj : j = 0
    · subst j
      simp
    · simp only [Function.update_of_ne hj]
      exact (h j hj).symm
  rw [ht, fiber_update_zero]

def localMatrices (U : Mat2) : Fin 6 → Mat2 := Function.update (fun _ => 1) 0 U

theorem local_unitary (U : Mat2) (hU : IsOneQubitUnitary U) (j : Fin 6) :
    IsOneQubitUnitary (localMatrices U j) := by
  by_cases hj : j = 0
  · subst j
    simpa [localMatrices] using hU
  · simp [localMatrices, Function.update_of_ne hj, IsOneQubitUnitary]

def transformedCode (W : Encoder) (U : Mat2) (hU : IsOneQubitUnitary U) :
    MainTheory.CodeSpec.ExactCode 6 2 3 :=
  unitaryCode (MainTheory.CompletionCodeBridge.code W) (localMatrices U) (local_unitary U hU)

theorem transformed_vec (W : Encoder) (U : Mat2) (hU : IsOneQubitUnitary U) (k : Fin 2) :
    (transformedCode W U hU).frame.vec k = kernelAction (oneQubitKernel 0 U) (W.states k) := by
  simp only [transformedCode, unitaryCode, unitaryFrame_vec]
  change kernelAction (tensorKernel (localMatrices U)) (W.states k) = _
  rw [localMatrices, tensorKernel_single]

def transform (W : Encoder) (U : Mat2) (hU : IsOneQubitUnitary U) : Encoder where
  states := (transformedCode W U hU).frame.vec
  supported := by
    intro k s hs
    rw [transformed_vec]
    unfold kernelAction
    apply Finset.sum_eq_zero
    intro t _
    by_cases hst : ∀ j, j ≠ (0 : Fin 6) → s j = t j
    · have ht : t ∉ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) := by
        intro ht
        exact hs ((fiber_spectator_invariant k s t hst).mpr ht)
      rw [W.supported k t ht, mul_zero]
    · simp only [oneQubitKernel, hst, if_false, zero_mul]
  normalized := by
    intro k
    exact ((transformedCode W U hU).frame.orthonormal k k).trans (if_pos rfl)
  hasDistance := (transformedCode W U hU).hasDistance

theorem transform_states (W : Encoder) (U : Mat2) (hU : IsOneQubitUnitary U) (k : Fin 2) :
    (transform W U hU).states k = kernelAction (oneQubitKernel 0 U) (W.states k) :=
  transformed_vec W U hU k

end
end MainTheory.Orbit3SpectatorUnitary
