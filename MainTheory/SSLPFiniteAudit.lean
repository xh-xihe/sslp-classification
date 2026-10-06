import MainTheory.GeneralFiniteness
import MainTheory.GeneralFinitenessRank
import MainTheory.SSLPCompleteness

/-! Every intrinsic class of every completed code is represented in the
same finite audit range used by the pipeline. -/

namespace MainTheory.SSLPFiniteAudit

open CodeSpec ClassificationLevels GlobalClassificationBridge BoundedRepresentation SSLPCompleteness

theorem representation_two {n d B : ℕ} (hd : 2 ≤ d)
    (beta : BinaryBeta.BetaBound (n+1) B) (hB : 0 < B) (C : ExactCode n 2 d) :
    HasBoundedRepresentation B C := by
  intro g
  by_cases hg : g = 1
  · subst g
    exact ⟨LabelledGates.trivialLabel hB, 1, rfl,
      by rw [LabelledGates.gateOfLabel_trivial]; rfl⟩
  · have hb : BinaryBeta.BetaBound (n+2-1) B := by simpa using beta
    obtain ⟨q, hlift, _, _, _, _, hqB⟩ :=
      QuantitativeGroup.quantitative_projective_group hb C hd g hg
    exact GeneralFinitenessRank.boundedLabel_of_hasPrimitiveLift hqB hlift

theorem representation_at_cutoff {n d B1 Bn : ℕ} (hd : 2 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n+1) B1) (betan : BinaryBeta.BetaBound n Bn)
    (hB1 : 0 < B1) (hBn : 0 < Bn) (C : ExactCode n 2 d) :
    HasBoundedRepresentation (outerCutoff B1 Bn d) C := by
  by_cases he : d = 2
  · have hc : outerCutoff B1 Bn d = B1 := by rw [he, outerCutoff_two]
    rw [hc]
    exact representation_two hd beta1 hB1 C
  · have h3 : 3 ≤ d := by omega
    rw [outerCutoff_of_three_le B1 Bn h3]
    exact GeneralFiniteness.hasBoundedRepresentation_general betan hBn (weakenDistance h3 C)

theorem audit_surjective {n d B1 Bn : ℕ} (hd : 2 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n+1) B1) (betan : BinaryBeta.BetaBound n Bn)
    (hB1 : 0 < B1) (hBn : 0 < Bn) (C : ExactCode n 2 d) :
    Function.Surjective (actionOfLabel (B := outerCutoff B1 Bn d) C) :=
  (coverOfRepresentation (representation_at_cutoff hd beta1 betan hB1 hBn C)).covers

end MainTheory.SSLPFiniteAudit
