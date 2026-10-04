import SixQubit.Generated.Orbit3CollectedKLRows
import SixQubit.Generated.Orbit3CollectedSpinRows
import SixQubit.Generated.Orbit3CollectedHadamardRows
import SixQubit.Generated.Orbit3CollectedTarget
import MainTheory.Orbit3TargetInterpretation
import MainTheory.Orbit3ScalarPlane
import MainTheory.EnumeratorLineAlgebra
import MainTheory.CompletionExactDistance
import MainTheory.Orbit3TargetClosure

/-! The orbit-3 enumerator image from actual complex KL completions. -/
namespace MainTheory.Orbit3FullImage

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3CoordinateRealization
open MainTheory.Orbit3TargetInterpretation MainTheory.Orbit3SamplingTarget
open MainTheory.DirectoryEnumeratorImages MainTheory.EnumeratorOrbitTransport
open SixQubit.Generated SS.MacWilliams
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

theorem row_kinds : ∀ i : Fin 211, Orbit3PauliConstraints.kind i = 0 ∨
    Orbit3PauliConstraints.kind i = 1 ∨ Orbit3PauliConstraints.kind i = 2 := by decide +kernel

theorem all_primitive_rows_zero (W : Encoder) (i : Fin 211) :
    Orbit3SexticIdentity.evaluate (Orbit3SexticIdentity.rows i) (coordinates W) = 0 := by
  rcases row_kinds i with h | h | h
  · exact Orbit3CollectedKLRows.all_kl_primitive_rows_zero W i h
  · exact Orbit3CollectedSpinRows.all_spin_primitive_rows_zero W i h
  · exact Orbit3CollectedHadamardRows.all_hadamard_primitive_rows_zero W i h

theorem target_coordinates (W : Encoder) :
    target W = Orbit3SexticIdentity.evaluate Orbit3SexticIdentity.target (coordinates W) :=
  MainTheory.Orbit3TargetClosure.target_coordinates W

theorem target_zero (W : Encoder) : target W = 0 := by
  rw [target_coordinates]
  exact Orbit3SexticIdentity.target_zero_of_constraints (coordinates W)
    (all_primitive_rows_zero W) (by rw [← target_coordinates]; exact target_nonneg W)
    (reduced_square_nonneg W)

theorem actual_A3_zero (W : Encoder) : Aco W.states 3 = 0 :=
  original_Aco_zero_of_target_zero W (target_zero W)

theorem exact_distance_three (W : Encoder) : ¬ SS.HasDistance W.states 4 :=
  MainTheory.CompletionExactDistance.not_distance_four W

theorem actual_enumerator (W : Encoder) :
    0 ≤ Aco W.states 1 / 4 ∧ Aco W.states 1 / 4 ≤ 1 ∧
      (fun w : Fin 7 => Aco W.states w / 4) =
        MainTheory.WImages.FI (Aco W.states 1 / 4) := by
  have h0 := SixQubit.Pin.Aco_zero W.states W.normalized
  obtain ⟨h4, h5, h6⟩ := macwilliams_six W.states W.hasDistance h0
  exact MainTheory.EnumeratorLineAlgebra.normalized_line (Aco W.states) h0
    (actual_A3_zero W) (MainTheory.Orbit3ScalarPlane.unnormalized_low_plane W)
    h4 h5 h6 (SixQubit.Pin.Aco_nonneg W.states 1) (SixQubit.Pin.Aco_nonneg W.states 2)

theorem directory_image : directoryImage 2 = MainTheory.WImages.FI '' Set.Icc (0 : ℝ) 1 := by
  apply Set.Subset.antisymm ?_ orbit3_attainment
  unfold directoryImage
  rw [completionImage_eq_of_fiberEquivalent orbit3_fibers]
  rintro A ⟨W, hW⟩
  obtain ⟨h0, h1, he⟩ := actual_enumerator W
  refine ⟨Aco W.states 1 / 4, ⟨h0, h1⟩, ?_⟩
  exact he.symm.trans (funext hW).symm

end
end MainTheory.Orbit3FullImage
