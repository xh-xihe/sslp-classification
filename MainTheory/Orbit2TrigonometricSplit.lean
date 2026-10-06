import Orbit2.Complete
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The exact W_theta isometry and its printed trigonometric enumerators. -/

namespace MainTheory.Orbit2TrigonometricSplit

noncomputable section

theorem half_norm (θ : ℝ) : Real.cos (θ/2)^2+Real.sin (θ/2)^2=1 := by
  nlinarith [Real.sin_sq_add_cos_sq (θ/2)]

theorem cos_difference (θ : ℝ) :
    Real.cos (θ/2)^2-Real.sin (θ/2)^2=Real.cos θ := by
  have h : Real.cos θ=2*Real.cos (θ/2)^2-1 := by
    calc _ = Real.cos (2*(θ/2)) := by congr 1; ring
      _ = _ := Real.cos_two_mul (θ/2)
  nlinarith [half_norm θ]

theorem sin_product (θ : ℝ) : 2*Real.cos (θ/2)*Real.sin (θ/2)=Real.sin θ := by
  calc _ = 2*Real.sin (θ/2)*Real.cos (θ/2) := by ring
    _ = Real.sin (2*(θ/2)) := (Real.sin_two_mul (θ/2)).symm
    _ = _ := by congr 1; ring

def W (θ : ℝ) : Matrix (Fin 4) (Fin 2) ℂ :=
  Orbit2.splitW (Real.cos (θ/2)) (Real.sin (θ/2))

theorem isometry (θ : ℝ) : (W θ).conjTranspose*W θ=1 :=
  Orbit2.split_isometry _ _ (half_norm θ)

theorem logical_lift (θ : ℝ) : Orbit2.zzFour*W θ=W θ*Orbit2.zTwo :=
  Orbit2.split_logical_lift _ _

theorem projection (θ : ℝ) :
    W θ*(W θ).conjTranspose=(1/2 : ℂ) •
      (1+(Real.cos θ : ℂ) • Orbit2.ziFour+(Real.sin θ : ℂ) • Orbit2.xxFour) := by
  rw [W,Orbit2.split_projection _ _ (half_norm θ),cos_difference,sin_product]

def encoder (θ : ℝ) : Orbit2.Encoder :=
  Orbit2.SplitSeed.encoder (Real.cos (θ/2)) (Real.sin (θ/2)) (half_norm θ)

theorem low_enumerators (θ : ℝ) : (encoder θ).A 1=Real.cos θ^2 ∧
    (encoder θ).A 2=Real.sin θ^2 ∧ (encoder θ).A 3=0 := by
  refine ⟨?_,?_,(encoder θ).A3_zero⟩
  · rw [encoder,Orbit2.SplitSeed.enumerator_one,cos_difference]
  · rw [encoder,Orbit2.SplitSeed.enumerator_two,sin_product]

theorem enumerator (θ : ℝ) :
    (fun w : Fin 7 => (encoder θ).A w.val)=Orbit2.enumeratorLine (Real.cos θ^2) := by
  rw [encoder,Orbit2.SplitSeed.enumerator_family,cos_difference]

end

end MainTheory.Orbit2TrigonometricSplit
