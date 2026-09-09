import SixQubit.K4Kernel
import SixQubit.Orbit36Phase

namespace MainTheory.Orbit36AlgebraDisplays

def walshMatrix : Matrix (Fin 3) (Fin 3) ℂ := !![-1,1,1;1,-1,1;1,1,-1]

theorem walsh_determinant : walshMatrix.det = 4 := by
  rw [Matrix.det_fin_three]
  change (-1 : ℂ)*(-1)*(-1) - (-1)*1*1 - 1*1*(-1) + 1*1*1 + 1*1*1 - 1*(-1)*1 = 4
  norm_num

theorem walsh_equations (d : Fin 3 → ℂ) : walshMatrix.mulVec d = 0 ↔
    -d 0 + d 1 + d 2 = 0 ∧ d 0 - d 1 + d 2 = 0 ∧ d 0 + d 1 - d 2 = 0 := by
  simp [funext_iff, Fin.forall_fin_succ, walshMatrix, dotProduct,
    Fin.sum_univ_succ, add_assoc, sub_eq_add_neg]

theorem K4_kernel_equations (c12 c13 c14 c23 c24 c34 : ℂ) (r : Fin 4 → ℂ) :
    (SixQubit.K4Kernel.K4 c12 c13 c14 c23 c24 c34).mulVec r = 0 ↔
      c12 * r 1 + c13 * r 2 + c14 * r 3 = 0 ∧
      c12 * r 0 + c23 * r 2 + c24 * r 3 = 0 ∧
      c13 * r 0 + c23 * r 1 + c34 * r 3 = 0 ∧
      c14 * r 0 + c24 * r 1 + c34 * r 2 = 0 := by
  simp [funext_iff, Fin.forall_fin_succ, SixQubit.K4Kernel.K4,
    dotProduct, Fin.sum_univ_succ, add_assoc]

theorem factorization_explicit {w12 w13 w14 w23 w24 w34 : ℝ}
    (p12 : 0 < w12) (p13 : 0 < w13) (p14 : 0 < w14) (p23 : 0 < w23)
    (h1 : w12 * w34 = w13 * w24) (h2 : w13 * w24 = w14 * w23) :
    let s1 := Real.sqrt (w12 * w13 / w23)
    let s2 := w12 / s1
    let s3 := w13 / s1
    let s4 := w14 / s1
    0 < s1 ∧ 0 < s2 ∧ 0 < s3 ∧ 0 < s4 ∧
      w12 = s1 * s2 ∧ w13 = s1 * s3 ∧ w14 = s1 * s4 ∧
      w23 = s2 * s3 ∧ w24 = s2 * s4 ∧ w34 = s3 * s4 := by
  dsimp only
  let s := Real.sqrt (w12 * w13 / w23)
  have ps : 0 < s := Real.sqrt_pos.mpr (div_pos (mul_pos p12 p13) p23)
  have hs : s * s = w12 * w13 / w23 := Real.mul_self_sqrt (by positivity)
  refine ⟨ps, div_pos p12 ps, div_pos p13 ps, div_pos p14 ps, ?_,?_,?_,?_,?_,?_⟩
  · exact (mul_div_cancel₀ _ ps.ne').symm
  · exact (mul_div_cancel₀ _ ps.ne').symm
  · exact (mul_div_cancel₀ _ ps.ne').symm
  all_goals change _ = _ / s * (_ / s)
  all_goals rw [div_mul_div_comm, hs]
  all_goals field_simp <;> nlinarith [h1, h2]

theorem degree_factor (s1 s2 s3 s4 : ℝ) :
    s1*s2+s1*s3+s1*s4 = s1 * (s1+s2+s3+s4-s1) := by ring

theorem common_cubic {s S p gamma : ℝ}
    (hD : p = s*(S-s)-1/10) (hg : p*s = gamma) :
    s^3-S*s^2+s/10+gamma=0 := by
  linear_combination s*hD-hg

theorem equal_scale_value {s : ℝ} (h : 6*s^2 = 2/5) : s^2 = 1/15 := by linarith

end MainTheory.Orbit36AlgebraDisplays
