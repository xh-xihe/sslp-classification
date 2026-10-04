import Orbit2.Complete

/-! Saturated shadow and complementary purities kill all extra low-weight mass. -/

namespace MainTheory.Orbit2OutsideActiveLow

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.PurityReduction Orbit2.PhysicalFlatness
open scoped BigOperators

def excess (V : Encoder) (p : Label 6) : ℝ :=
  (if physicalWeight p≤3 then physicalMass V p else 0)-
    (if supported (Fin.cons (0 : Fin 4) p) A then physicalMass V p else 0)

theorem excess_nonneg (V : Encoder) (p : Label 6) : 0≤excess V p := by
  unfold excess
  by_cases hs : supported (Fin.cons (0 : Fin 4) p) A
  · by_cases hw : physicalWeight p≤3
    · simp [hs,hw]
    · rw [active_supported_high_zero V p hs (by omega)]
      simp
  · by_cases hw : physicalWeight p≤3
    · simpa [hs,hw] using physicalMass_nonneg V p
    · simp [hs,hw]

theorem excess_sum_zero (V : Encoder) : ∑ p : Label 6,excess V p=0 := by
  unfold excess
  rw [Finset.sum_sub_distrib,low_weight_partition,← active_projection,active_mass,V.A_zero]
  linarith [V.flat]

theorem mass_zero (V : Encoder) (p : Label 6) (hw : physicalWeight p≤3)
    (hs : ¬supported (Fin.cons (0 : Fin 4) p) A) : physicalMass V p=0 := by
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => excess_nonneg V q)).mp
    (excess_sum_zero V)
  simpa only [excess,if_pos hw,if_neg hs,sub_zero] using h p (Finset.mem_univ p)

theorem coefficient_zero (V : Encoder) (p : Label 6) (hw : physicalWeight p≤3)
    (hs : ¬supported (Fin.cons (0 : Fin 4) p) A) :
    SS.MacWilliams.trProj V.psi (Orbit2.decode p)=0 := by
  have h := mass_zero V p hw hs
  unfold physicalMass at h
  exact Complex.normSq_eq_zero.mp (by linarith)

end

end MainTheory.Orbit2OutsideActiveLow
