import MainTheory.Orbit2StandardFiveQubit

/-! Normalized physical five-qubit states, full KL, and local Clifford transport. -/

namespace MainTheory.Orbit2StandardSeedBridge

noncomputable section

open MainTheory.Orbit2StandardFiveQubit Orbit2.TensorPauli
open scoped BigOperators

theorem operator_standard (p : Label 5) (j : Fin 2) (s : Fin 5 → Fin 2) :
    (∑ t,operator p s t*(standard j t : ℂ))=(Orbit2.FiveQubit.act p (standard j) s : ℂ) := by
  simp_rw [Orbit2.FiveQubit.operator_row]
  simp [Orbit2.FiveQubit.act,GaussianInt.toComplex_mul]

theorem code_action (p : Label 5) :
    operator p*code=fun s j => (Orbit2.FiveQubit.act p (standard j) s : ℂ)/4 := by
  ext s j
  simp only [Matrix.mul_apply,code,← mul_div_assoc,← Finset.sum_div]
  rw [operator_standard]

theorem code_pure_KL (p : Label 5) (hp : Orbit2.FiveQubit.weight p ≤ 2) :
    code.conjTranspose*operator p*code=if p=(fun _ => 0) then 1 else 0 := by
  rw [Matrix.mul_assoc,code_action]
  ext j k
  calc
    _ = ((∑ s,star (standard j s)*Orbit2.FiveQubit.act p (standard k) s : GaussianInt) : ℂ)/16 := by
      simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,code,map_sum,
        GaussianInt.toComplex_mul,GaussianInt.toComplex_star,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro s _
      simp only [star_div₀,star_ofNat,starRingEnd_apply]
      ring
    _ = _ := by
      rw [standard_pure_KL_G p hp j k]
      by_cases h : p=(fun _ => 0)
      all_goals by_cases hj : j=k
      all_goals norm_num [h,hj,Matrix.one_apply,GaussianInt.toComplex_def]

theorem code_isometry : code.conjTranspose*code=1 := by
  have h := code_pure_KL (fun _ => 0) (by simp [Orbit2.FiveQubit.weight])
  simpa [operator_zero] using h

theorem code_stabilizers (g : Fin 4) : operator (generators g)*code=code := by
  rw [code_action]
  ext s j
  rw [fixed_generators]
  rfl

def rotate (site : Fin 5) (v : (Fin 5 → Fin 2) → ℂ) (s : Fin 5 → Fin 2) : ℂ :=
  ∑ r : Fin 2,Orbit2StandardFiveQubit.rotation (s site) r*v (Function.update s site r)

theorem rotate_scale (site : Fin 5) (c : ℂ) (v : (Fin 5 → Fin 2) → ℂ)
    (s : Fin 5 → Fin 2) : rotate site (fun t => c*v t) s=c*rotate site v s := by
  unfold rotate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem rotate_integer (site : Fin 5) (v : (Fin 5 → Fin 2) → GaussianInt)
    (s : Fin 5 → Fin 2) :
    rotate site (fun t => (v t : ℂ)) s=(Real.sqrt 2 : ℂ)⁻¹*(rotateG site v s : ℂ) := by
  simp only [rotate,Orbit2StandardFiveQubit.rotation,Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,
    rotateG,map_sum,GaussianInt.toComplex_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem normalized_transport (j : Fin 2) (s : Fin 5 → Fin 2) :
    rotate 3 (rotate 0 (fun t => code t (if j=0 then 1 else 0))) (permuteBits s)=
      Orbit2.FiveQubit.code s j := by
  have hinner : rotate 0 (fun t => code t (if j=0 then 1 else 0))=
      fun t => ((4 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹)*
        (rotateG 0 (standard (if j=0 then 1 else 0)) t : ℂ) := by
    funext t
    have hc : (fun t => code t (if j=0 then 1 else 0))=
        fun t => (4 : ℂ)⁻¹*(standard (if j=0 then 1 else 0) t : ℂ) := by
      funext t
      simp only [code,div_eq_mul_inv]
      ring
    rw [hc,rotate_scale,rotate_integer]
    ring
  rw [hinner,rotate_scale,rotate_integer,seed_transport]
  have hc : ((4 : ℂ)⁻¹*(Real.sqrt 2 : ℂ)⁻¹)*(Real.sqrt 2 : ℂ)⁻¹=(8 : ℂ)⁻¹ := by
    calc _ = (4 : ℂ)⁻¹*((Real.sqrt 2 : ℂ)^2)⁻¹ := by rw [← inv_pow]; ring
      _ = _ := by rw [sqrt_squared]; norm_num
  rw [← mul_assoc,hc]
  simp only [Orbit2.FiveQubit.code,div_eq_mul_inv]
  ring

end

end MainTheory.Orbit2StandardSeedBridge
