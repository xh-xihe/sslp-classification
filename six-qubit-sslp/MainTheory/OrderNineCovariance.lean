import MainTheory.OrderNineMomentStatistics

namespace MainTheory.OrderNineCovariance

open MainTheory.OrderNineMomentStatistics MainTheory.CodeAffineSpanBridge

noncomputable def covariance : Matrix (Fin 6) (Fin 6) ℝ :=
  MainTheory.Covariance.cov (fun i => (weights i : ℝ))
    (fun i => bitPoint (vertices i)) (fun _ => 1/2)

theorem determinant_exact : covariance.det = 5/157464 := by
  rw [covariance, real_covariance]
  calc
    (displayedCovariance.map (algebraMap ℚ ℝ)).det = (displayedCovariance.det : ℝ) :=
      ((algebraMap ℚ ℝ).map_det displayedCovariance).symm
    _ = 5/157464 := by rw [← covariance_exact, covariance_det]; norm_num

theorem determinant_positive : 0 < covariance.det := by rw [determinant_exact]; norm_num

theorem full_rank : covariance.rank = 6 := by
  have hu : IsUnit covariance := (Matrix.isUnit_iff_isUnit_det covariance).mpr
    (isUnit_iff_ne_zero.mpr (ne_of_gt determinant_positive))
  simpa using Matrix.rank_of_isUnit covariance hu

theorem complementary_covariance : MainTheory.Covariance.cov
    (fun i => (weights i : ℝ))
    (fun i => bitPoint (SS.complement (vertices i))) (fun _ => 1/2) = covariance := by
  ext j k
  unfold MainTheory.Covariance.cov covariance
  apply Finset.sum_congr rfl
  intro i _
  have hc (j : Fin 6) : bitPoint (SS.complement (vertices i)) j = 1 - bitPoint (vertices i) j := by
    cases hv : vertices i j <;> simp [bitPoint, SS.complement, hv]
  change (weights i : ℝ) * (bitPoint (SS.complement (vertices i)) j - 1/2) *
      (bitPoint (SS.complement (vertices i)) k - 1/2) = _
  rw [hc, hc]
  ring

end MainTheory.OrderNineCovariance
