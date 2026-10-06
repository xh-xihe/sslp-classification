import MainTheory.CovarianceRange
import MainTheory.RealSupportAffineRank

namespace MainTheory.NormalizedSupportCovariance

open MainTheory.CodeAffineSpanBridge MainTheory.RealSupportAffineRank

variable {n : ℕ}

theorem direction_eq_covariance_range (c : SS.State n ℂ) (hc : SS.innerC c c = 1) :
    (affineSpan ℝ (supportPointSet c)).direction =
      LinearMap.range (Matrix.mulVecLin (stateCovariance c)) := by
  have hm := MainTheory.Covariance.weightedMean_mem_affineSpan
    (supportProbability c) (supportPoint c) (stateMean c)
    (sum_supportProbability_eq_one c hc) rfl
  have h := MainTheory.CovarianceRange.affineSpan_eq_mu_add_range
    (supportProbability c) (supportPoint c) (stateMean c) (supportProbability_pos c) hm
  simpa only [range_supportPoint, supportPointSet, stateCovariance] using h

theorem supports_in_covariance_range {c d : SS.State n ℂ}
    (hc : SS.innerC c c = 1) (hzero : c (fun _ => false) ≠ 0)
    (H : CommonAffineSpanCertificate c d) :
    ∀ x, x ∈ actualSupport c ∪ actualSupport d →
      bitPoint x ∈ LinearMap.range (Matrix.mulVecLin (stateCovariance c)) := by
  intro x hx
  rw [← direction_eq_covariance_range c hc]
  have h0 : (0 : Fin n → ℝ) ∈ affineSpan ℝ (supportPointSet c) :=
    mem_affineSpan ℝ ⟨fun _ => false, hzero,
      MainTheory.SixQubitSemanticEntrance.bitPoint_zeroBitString⟩
  have hx' : bitPoint x ∈ affineSpan ℝ (supportPointSet c) := by
    rcases hx with hx | hx
    · exact mem_affineSpan ℝ ⟨x, hx, rfl⟩
    · change bitPoint x ∈ affineSpan ℝ (bitPoint '' actualSupport c)
      rw [H.affineSpan_eq]
      exact mem_affineSpan ℝ ⟨x, hx, rfl⟩
  simpa using AffineSubspace.vsub_mem_direction hx' h0

theorem covariance_range_dimension (c : SS.State n ℂ) (hc : SS.innerC c c = 1) :
    Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin (stateCovariance c))) =
      supportAffineRank c := by
  rw [← direction_eq_covariance_range c hc]
  rfl

theorem covariance_range_eq_span_differences (c : SS.State n ℂ)
    (hc : SS.innerC c c = 1) :
    LinearMap.range (Matrix.mulVecLin (stateCovariance c)) =
      Submodule.span ℝ (supportPointSet c -ᵥ supportPointSet c) := by
  rw [← direction_eq_covariance_range c hc, direction_affineSpan, vectorSpan_def]

end MainTheory.NormalizedSupportCovariance
