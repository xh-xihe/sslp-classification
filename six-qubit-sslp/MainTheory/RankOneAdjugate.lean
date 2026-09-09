import Mathlib

set_option autoImplicit false

namespace MainTheory.RankOneAdjugate

theorem kernel_span_of_succ_minor {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (r : Fin (n+1) → ℂ) (hr : A.mulVec r = 0) (hr0 : r 0 ≠ 0)
    (hminor : (A.submatrix Fin.succ Fin.succ).det ≠ 0) :
    ∀ v, A.mulVec v = 0 → ∃ c : ℂ, v = c • r := by
  intro v hv
  let c := v 0 / r 0
  let w := v - c • r
  have hw : A.mulVec w = 0 := by
    simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul, hv, hr, smul_zero, sub_zero]
  have hw0 : w 0 = 0 := by simp [w, c, hr0]
  have hm : (A.submatrix Fin.succ Fin.succ).mulVec (fun j => w j.succ) = 0 := by
    funext i
    have h := congrFun hw i.succ
    change (∑ j, A i.succ j * w j) = 0 at h
    rw [Fin.sum_univ_succ, hw0, mul_zero, zero_add] at h
    exact h
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det (A.submatrix Fin.succ Fin.succ)).mpr
      (isUnit_iff_ne_zero.mpr hminor))
  have hrest : (fun j : Fin n => w j.succ) = 0 := hi (hm.trans (Matrix.mulVec_zero _).symm)
  have hzero : w = 0 := by
    funext j
    refine Fin.cases hw0 (fun i => congrFun hrest i) j
  exact ⟨c, sub_eq_zero.mp hzero⟩

theorem adjugate_rank_one {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hsym : A.IsSymm) (hdet : A.det = 0) (r : Fin (n+1) → ℂ)
    (hr0 : r 0 ≠ 0)
    (hspan : ∀ v, A.mulVec v = 0 → ∃ c : ℂ, v = c • r) :
    ∃ kappa : ℂ, A.adjugate = fun i j => kappa * (r i * r j) := by
  have hcol (j : Fin (n+1)) : ∃ c : ℂ, (fun i => A.adjugate i j) = c • r := by
    apply hspan
    funext i
    have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℂ => M i j)
      (Matrix.mul_adjugate A)
    simpa [hdet, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  choose c hc using hcol
  have he (i j : Fin (n+1)) : A.adjugate i j = c j * r i := congrFun (hc j) i
  have hsymadj : A.adjugate.IsSymm := hsym.adjugate
  have hcoeff (j : Fin (n+1)) : c j * r 0 = c 0 * r j := by
    rw [← he, ← he]
    exact (hsymadj.apply 0 j).symm
  refine ⟨c 0 / r 0, ?_⟩
  ext i j
  rw [he]
  field_simp
  linear_combination r i * hcoeff j

end MainTheory.RankOneAdjugate
