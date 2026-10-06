import MainTheory.RankOneAdjugate
import SixQubit.K4Kernel

set_option autoImplicit false

namespace MainTheory.Orbit36Adjugate

open SixQubit.K4Kernel

theorem symmetric (c12 c13 c14 c23 c24 c34 : ℂ) :
    (K4 c12 c13 c14 c23 c24 c34).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem minor_determinant (c12 c13 c14 c23 c24 c34 : ℂ) :
    ((K4 c12 c13 c14 c23 c24 c34).submatrix Fin.succ Fin.succ).det =
      2*c23*c24*c34 := by
  rw [Matrix.det_fin_three]
  change (0 : ℂ)*0*0 - 0*c34*c34 - c23*c23*0 + c23*c34*c24 + c24*c23*c34 - c24*0*c24 = _
  ring

theorem adjugate_factorization (c12 c13 c14 c23 c24 c34 : ℂ)
    (r : Fin 4 → ℂ) (hr0 : r 0 ≠ 0)
    (h23 : c23 ≠ 0) (h24 : c24 ≠ 0) (h34 : c34 ≠ 0)
    (hr : (K4 c12 c13 c14 c23 c24 c34).mulVec r = 0) :
    ∃ kappa : ℂ, (K4 c12 c13 c14 c23 c24 c34).adjugate =
      fun i j => kappa * (r i * r j) := by
  have hminor : ((K4 c12 c13 c14 c23 c24 c34).submatrix Fin.succ Fin.succ).det ≠ 0 := by
    rw [minor_determinant]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h23) h24) h34
  have hrne : r ≠ 0 := by intro h; exact hr0 (congrFun h 0)
  have hdet : (K4 c12 c13 c14 c23 c24 c34).det = 0 := by
    by_contra h
    have hi := Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h))
    exact hrne (hi (hr.trans (Matrix.mulVec_zero _).symm))
  exact MainTheory.RankOneAdjugate.adjugate_rank_one _ (symmetric ..) hdet r hr0
    (MainTheory.RankOneAdjugate.kernel_span_of_succ_minor _ r hr hr0 hminor)

theorem diagonal_cofactors (c12 c13 c14 c23 c24 c34 : ℂ) : ∀ i : Fin 4,
    (K4 c12 c13 c14 c23 c24 c34).adjugate i i =
      ![2*c23*c24*c34, 2*c13*c14*c34, 2*c12*c14*c24, 2*c12*c13*c23] i := by
  intro i
  fin_cases i <;>
    simp +decide [K4, Matrix.adjugate_fin_succ_eq_det_submatrix,
      Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove] <;> ring

theorem triangle_cofactor_norm {a b c : ℂ} {s1 s2 s3 : ℝ}
    (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3)
    (ha : Complex.normSq a = s1*s2) (hb : Complex.normSq b = s1*s3)
    (hc : Complex.normSq c = s2*s3) : ‖2*a*b*c‖ = 2*s1*s2*s3 := by
  have hn : ‖2*a*b*c‖^2 = (2*s1*s2*s3)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [map_mul, ha, hb, hc]
    norm_num
    ring
  have hp : 0 ≤ 2*s1*s2*s3 := by positivity
  nlinarith [norm_nonneg (2*a*b*c)]

theorem probability_scale_constant {kappa : ℂ} (r : Fin 4 → ℂ) (s : Fin 4 → ℝ)
    (hs : ∀ i, 0 < s i)
    (hdiag : ∀ i, ‖kappa * (r i * r i)‖ = 2 * ∏ j ∈ Finset.univ.erase i, s j) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ i, Complex.normSq (r i) * s i = gamma := by
  have hpos (i : Fin 4) : 0 < ∏ j ∈ Finset.univ.erase i, s j :=
    Finset.prod_pos (fun j _ => hs j)
  have hk : 0 < ‖kappa‖ := by
    have hh := hdiag 0
    rw [norm_mul] at hh
    by_contra h
    have hz : ‖kappa‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz, zero_mul] at hh
    linarith [hpos 0]
  refine ⟨2 * (∏ j, s j) / ‖kappa‖, ?_, ?_⟩
  · exact div_pos (mul_pos (by norm_num) (Finset.prod_pos (fun j _ => hs j))) hk
  intro i
  apply (eq_div_iff hk.ne').mpr
  have hh := hdiag i
  rw [norm_mul, norm_mul, ← pow_two, ← Complex.normSq_eq_norm_sq] at hh
  have hprod := Finset.prod_erase_mul (s := Finset.univ) s (Finset.mem_univ i)
  linear_combination s i * hh + 2 * hprod

theorem nonzero_adjugate_factorization (c12 c13 c14 c23 c24 c34 : ℂ)
    (r : Fin 4 → ℂ) (hr0 : r 0 ≠ 0)
    (h23 : c23 ≠ 0) (h24 : c24 ≠ 0) (h34 : c34 ≠ 0)
    (hr : (K4 c12 c13 c14 c23 c24 c34).mulVec r = 0) :
    ∃ kappa : ℂ, kappa ≠ 0 ∧ (K4 c12 c13 c14 c23 c24 c34).adjugate =
      fun i j => kappa * (r i * r j) := by
  obtain ⟨kappa,hk⟩ := adjugate_factorization c12 c13 c14 c23 c24 c34 r hr0 h23 h24 h34 hr
  refine ⟨kappa, ?_, hk⟩
  intro hz
  have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) hk
  dsimp only at hh
  rw [diagonal_cofactors] at hh
  change 2*c23*c24*c34 = kappa * (r 0 * r 0) at hh
  rw [hz, zero_mul] at hh
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h23) h24) h34) hh

theorem kernel_and_rank (c12 c13 c14 c23 c24 c34 : ℂ)
    (r : Fin 4 → ℂ) (hr0 : r 0 ≠ 0)
    (h23 : c23 ≠ 0) (h24 : c24 ≠ 0) (h34 : c34 ≠ 0)
    (hr : (K4 c12 c13 c14 c23 c24 c34).mulVec r = 0) :
    LinearMap.ker (K4 c12 c13 c14 c23 c24 c34).mulVecLin = Submodule.span ℂ {r} ∧
      (K4 c12 c13 c14 c23 c24 c34).rank = 3 := by
  let A := K4 c12 c13 c14 c23 c24 c34
  have hminor : (A.submatrix Fin.succ Fin.succ).det ≠ 0 := by
    rw [minor_determinant]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h23) h24) h34
  have hspan := MainTheory.RankOneAdjugate.kernel_span_of_succ_minor A r hr hr0 hminor
  have hker : LinearMap.ker A.mulVecLin = Submodule.span ℂ {r} := by
    ext v
    constructor
    · intro hv
      obtain ⟨c,hc⟩ := hspan v hv
      exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩
    · intro hv
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv
      rw [← hc]
      change A.mulVec (c • r) = 0
      rw [Matrix.mulVec_smul, hr, smul_zero]
  refine ⟨hker, ?_⟩
  have hrne : r ≠ 0 := by intro h; exact hr0 (congrFun h 0)
  have hdim := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [hker, finrank_span_singleton hrne] at hdim
  change A.rank = 3
  simpa using hdim

end MainTheory.Orbit36Adjugate
