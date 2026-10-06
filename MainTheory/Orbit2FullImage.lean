import Orbit2.Complete
import MainTheory.CompletionCodeBridge
import MainTheory.OrderTwoScalarBridge

/-! The orbit-2 converse for the actual completions in the orbit directory. -/
namespace MainTheory.Orbit2FullImage

open MainTheory.CubeCompletionTransport MainTheory.DirectoryEnumeratorImages
open MainTheory.EnumeratorOrbitTransport SixQubit.ParityPauliScalars SS.MacWilliams

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

abbrev Encoder := Completion (angleFibers SixQubit.OpenLOrbit2.angle)

theorem mask_eq : MainTheory.OrderTwoScalarBridge.orbit2Mask =
    ![false, false, true, true, true, true] := by decide +kernel

theorem logicalZ (W : Encoder) (j : Fin 2) :
    SS.pauliAct
      (⟨fun _ => false, ![false, false, true, true, true, true]⟩ : SS.PauliString 6)
      (W.states j) = fun x => (if j = 0 then 1 else -1) * W.states j x := by
  funext x
  have hp := MainTheory.OrderTwoScalarBridge.orbit2_parity W j
  rw [mask_eq] at hp
  have hn : (⟨fun _ => false, ![false, false, true, true, true, true]⟩ : SS.PauliString 6).numY = 0 := by
    simp [SS.PauliString.numY]
  simp only [SS.pauliAct, hn, pow_zero, one_mul, SS.bxor_zero]
  rw [SS.MacWilliams.signC_bdot]
  by_cases h : chi ![false, false, true, true, true, true] x = logicalSign j
  · rw [h]
    by_cases hj : j = 0 <;> simp [logicalSign, hj]
  · rw [hp x h]
    simp

def toOrbit2 (W : Encoder) : Orbit2.Encoder where
  psi := W.states
  orthonormal := MainTheory.CompletionCodeBridge.orthonormal W
  detects := W.hasDistance
  logicalZ := logicalZ W

theorem actual_enumerator (W : Encoder) :
    0 ≤ Aco W.states 1 / 4 ∧ Aco W.states 1 / 4 ≤ 1 ∧
      (fun w : Fin 7 => Aco W.states w / 4) =
        MainTheory.WImages.FI (Aco W.states 1 / 4) := by
  simpa only [Orbit2.Encoder.A, toOrbit2, Orbit2.enumeratorLine,
    MainTheory.WImages.FI] using (toOrbit2 W).enumerator

theorem actual_A3_zero (W : Encoder) : Aco W.states 3 = 0 := by
  have h := (toOrbit2 W).A3_zero
  change Aco W.states 3 / 4 = 0 at h
  linarith

theorem exact_distance_three (W : Encoder) : ¬ SS.HasDistance W.states 4 :=
  (toOrbit2 W).exact_distance_three

theorem directory_image : directoryImage 1 = MainTheory.WImages.FI '' Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm ?_ orbit2_attainment
  unfold directoryImage
  rw [completionImage_eq_of_fiberEquivalent orbit2_fibers]
  rintro A ⟨W, hW⟩
  obtain ⟨h0, h1, he⟩ := actual_enumerator W
  refine ⟨Aco W.states 1 / 4, ⟨h0, h1⟩, ?_⟩
  exact he.symm.trans (funext hW).symm

end
end MainTheory.Orbit2FullImage
