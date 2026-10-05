import MainTheory.Orbit2StandardFiveQubit

/-! The printed four-generator perfect code, with its normalized physical
projector and all weight-one/two Pauli compressions.
-/

namespace MainTheory.StandardPerfectCodePhysical
open MainTheory.Orbit2StandardFiveQubit Orbit2.FiveQubit Orbit2.TensorPauli
open scoped BigOperators
noncomputable section

theorem standard_action (p : Label 5) :
    operator p*MainTheory.Orbit2StandardFiveQubit.code=
      fun s j => (act p (standard j) s : ℂ)/4 := by
  ext s j
  simp only [Matrix.mul_apply,MainTheory.Orbit2StandardFiveQubit.code,
    ← mul_div_assoc,← Finset.sum_div]
  simp_rw [operator_row]
  simp [act,GaussianInt.toComplex_mul]

theorem compression (p : Label 5) (hp : weight p≤2) :
    MainTheory.Orbit2StandardFiveQubit.code.conjTranspose*operator p*
      MainTheory.Orbit2StandardFiveQubit.code=if p=(fun _ => 0) then 1 else 0 := by
  rw [Matrix.mul_assoc,standard_action]
  ext j k
  calc
    _ = ((∑ s,star (standard j s)*act p (standard k) s : GaussianInt) : ℂ)/16 := by
      simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,
        MainTheory.Orbit2StandardFiveQubit.code,map_sum,GaussianInt.toComplex_mul,
        GaussianInt.toComplex_star,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      simp only [star_div₀,star_ofNat,starRingEnd_apply]
      ring
    _ = _ := by
      rw [standard_pure_KL_G p hp j k]
      by_cases h : p=fun _ => 0 <;> by_cases hj : j=k <;>
        norm_num [h,hj,Matrix.one_apply,GaussianInt.toComplex_def]

theorem isometry : MainTheory.Orbit2StandardFiveQubit.code.conjTranspose*
    MainTheory.Orbit2StandardFiveQubit.code=1 := by
  simpa [operator_zero] using compression (fun _ => 0) (by simp [weight])

def projector := MainTheory.Orbit2StandardFiveQubit.code*
  MainTheory.Orbit2StandardFiveQubit.code.conjTranspose

theorem projector_idempotent : projector*projector=projector := by
  simp only [projector,Matrix.mul_assoc,← Matrix.mul_assoc
    MainTheory.Orbit2StandardFiveQubit.code.conjTranspose
    MainTheory.Orbit2StandardFiveQubit.code,isometry,Matrix.one_mul]

theorem pure_projector (p : Label 5) (hp : weight p≤2) (hne : p≠fun _ => 0) :
    projector*operator p*projector=0 := by
  calc
    _ = MainTheory.Orbit2StandardFiveQubit.code*
      (MainTheory.Orbit2StandardFiveQubit.code.conjTranspose*operator p*
        MainTheory.Orbit2StandardFiveQubit.code)*
      MainTheory.Orbit2StandardFiveQubit.code.conjTranspose := by
        simp only [projector,Matrix.mul_assoc]
    _ = _ := by rw [compression p hp,if_neg hne,Matrix.mul_zero,Matrix.zero_mul]

theorem generators_fix (g : Fin 4) :
    operator (generators g)*MainTheory.Orbit2StandardFiveQubit.code=
      MainTheory.Orbit2StandardFiveQubit.code := by
  rw [standard_action]
  ext s j
  rw [fixed_generators]
  rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
theorem small_anticommuting_generator : ∀ p : Label 5,weight p≤2 →
    p≠(fun _ => 0) → ∃ g : Fin 4,
      phase (generators g) p= -phase p (generators g) := by
  decide +kernel

end
end MainTheory.StandardPerfectCodePhysical
