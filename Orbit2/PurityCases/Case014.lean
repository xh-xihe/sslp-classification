import Orbit2.PurityDefinitions
namespace Orbit2.PurityReduction.Case014
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem checked : ∀ a : Orbit2.TensorPauli.Label 4,
    let p := packed 0 3 2 a
    ¬ (forbidden p ∨ forbidden (partner p)) →
    purityCoefficient p + purityCoefficient (partner p) =
      -4 * (targetCoefficient p + targetCoefficient (partner p)) := by
  decide +kernel
end Orbit2.PurityReduction.Case014
