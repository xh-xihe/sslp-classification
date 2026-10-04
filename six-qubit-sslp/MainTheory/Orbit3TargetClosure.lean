import SixQubit.Generated.Orbit3CollectedTarget
import MainTheory.Orbit3TargetInterpretation

/-! All 120 target Paulis realize the exact target on actual encoders. -/
namespace MainTheory.Orbit3TargetClosure

open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3CoordinateRealization
open MainTheory.Orbit3TargetInterpretation MainTheory.Orbit3SamplingTarget
open SixQubit.Generated
noncomputable section

theorem target_coordinates (W : Encoder) :
    target W = Orbit3SexticIdentity.evaluate Orbit3SexticIdentity.target (coordinates W) := by
  rw [target_eq_raw]
  simp_rw [← Orbit3CollectedTarget.all_evaluations]
  exact collected_sum _

end
end MainTheory.Orbit3TargetClosure
