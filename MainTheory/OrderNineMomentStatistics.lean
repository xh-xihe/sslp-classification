import SixQubit.Order9
import MainTheory.MomentMatrix23
import MainTheory.CodeAffineSpanBridge

namespace MainTheory.OrderNineMomentStatistics

open SixQubit.Order9 MainTheory.FiniteMomentMatrix

def vertices : Fin 7 → SS.BitString 6 := ![y0, y1, y2, y3, y4, y5, y6]
def weights : Fin 7 → ℚ := ![2/9, 1/18, 1/18, 1/6, 1/9, 1/9, 5/18]
def pointQ (i : Fin 7) (j : Fin 6) : ℚ := if vertices i j then 1 else 0
def meanQ (j : Fin 6) : ℚ := ∑ i, weights i * pointQ i j
def covarianceQ : Matrix (Fin 6) (Fin 6) ℚ :=
  fun j k => ∑ i, weights i * (pointQ i j - meanQ j) * (pointQ i k - meanQ k)
def displayedCovariance : Matrix (Fin 6) (Fin 6) ℚ := (1/36 : ℚ) •
  !![9,-1,-1,-1,-1,-1;
    -1,9,5,3,3,5;
    -1,5,9,3,3,5;
    -1,3,3,9,7,1;
    -1,3,3,7,9,1;
    -1,5,5,1,1,9]

theorem angle_sum : (∑ j, (av j).val) = 19 := by decide +kernel
theorem angle_sum_mod : (∑ j, av j) = 1 := by decide +kernel
theorem complement_weight : ∀ x : SS.BitString 6,
    SS.weight av (SS.complement x) = 1 - SS.weight av x := by decide +kernel
theorem vertices_exact : Finset.univ.image vertices = S0 := by decide +kernel
theorem vertices_injective : Function.Injective vertices := by decide +kernel
theorem fiber_cards : S0.card = 7 ∧ S1.card = 7 := by decide +kernel
theorem weights_positive : ∀ i, 0 < weights i := by decide +kernel
theorem weights_normalized : ∑ i, weights i = 1 := by decide +kernel
theorem mean_exact : meanQ = fun _ => 1/2 := by decide +kernel
theorem covariance_exact : covarianceQ = displayedCovariance := by decide +kernel
theorem covariance_det : covarianceQ.det = 5/157464 := by
  rw [covariance_exact]
  decide +kernel

def word (x : SS.BitString 6) : MainTheory.FinitePipeline.Word6 :=
  (BitVec.ofFnLE x).toFin
def leftWords : Fin 7 → MainTheory.FinitePipeline.Word6 := fun i => word (vertices i)
def rightWords : Fin 7 → MainTheory.FinitePipeline.Word6 := fun i => word (SS.complement (vertices i))
def probability : Sum (Fin 7) (Fin 7) → ℚ := Sum.elim weights weights

theorem moment_feasible : MainTheory.ExactLP.Feasible
    (MainTheory.MomentMatrix23.matrixQ leftWords rightWords) rhsQ probability := by
  constructor <;> decide +kernel

theorem real_covariance : MainTheory.Covariance.cov
    (fun i => (weights i : ℝ))
    (fun i => MainTheory.CodeAffineSpanBridge.bitPoint (vertices i)) (fun _ => 1/2) =
      displayedCovariance.map (algebraMap ℚ ℝ) := by
  ext j k
  have h := congrArg (fun A : Matrix (Fin 6) (Fin 6) ℚ => (A j k : ℝ)) covariance_exact
  simp only [covarianceQ] at h
  rw [mean_exact] at h
  change (∑ i, (weights i : ℝ) *
    (MainTheory.CodeAffineSpanBridge.bitPoint (vertices i) j - 1/2) *
    (MainTheory.CodeAffineSpanBridge.bitPoint (vertices i) k - 1/2)) = _
  have hpoint (i : Fin 7) (j : Fin 6) : (pointQ i j : ℝ) =
      MainTheory.CodeAffineSpanBridge.bitPoint (vertices i) j := by
    cases hv : vertices i j <;> simp [pointQ, MainTheory.CodeAffineSpanBridge.bitPoint, hv]
  push_cast at h
  simpa only [hpoint] using h

end MainTheory.OrderNineMomentStatistics
