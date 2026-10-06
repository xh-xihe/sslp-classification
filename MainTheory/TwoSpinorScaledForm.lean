import MainTheory.TwoSpinorStandardForm

set_option autoImplicit false

namespace MainTheory.TwoSpinorNormalization

theorem scaled_standard_form (u v : Vec) (r : ℝ) (hr : 0 < r)
    (hu : Complex.normSq (u 0) + Complex.normSq (u 1) = r^2)
    (hv : Complex.normSq (v 0) + Complex.normSq (v 1) = r^2) :
    ∃ (T : Mat) (lambda : ℂ) (c : ℝ),
      T * T.conjTranspose = 1 ∧ T.conjTranspose * T = 1 ∧
      Complex.normSq lambda = 1 ∧ 0 ≤ c ∧ c ≤ 1 ∧
      (fun i => lambda * (T.mulVec u i)) = ![(r : ℂ),0] ∧
      T.mulVec v = ![((r*c : ℝ) : ℂ),((r*Real.sqrt (1-c^2) : ℝ) : ℂ)] := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hnorm (s : Vec) (hs : Complex.normSq (s 0) + Complex.normSq (s 1) = r^2) :
      Complex.normSq (s 0/(r : ℂ)) + Complex.normSq (s 1/(r : ℂ)) = 1 := by
    simp only [map_div₀,Complex.normSq_ofReal,← add_div]
    rw [hs]
    field_simp
  obtain ⟨T,lambda,c,hT,hT',hl,hc0,hc1,hu',hv'⟩ :=
    standard_form (fun i => u i/(r : ℂ)) (fun i => v i/(r : ℂ)) (hnorm u hu) (hnorm v hv)
  have hquot (s : Vec) : T.mulVec (fun i => s i/(r : ℂ)) =
      fun i => T.mulVec s i/(r : ℂ) := by
    funext i
    simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  rw [hquot] at hu' hv'
  refine ⟨T,lambda,c,hT,hT',hl,hc0,hc1,?_,?_⟩
  · funext i
    have h := congrFun hu' i
    fin_cases i <;> norm_num at h ⊢
    · field_simp at h
      simpa [hr.ne'] using h
    · field_simp at h
      simpa [hr.ne'] using h
  · funext i
    have h := congrFun hv' i
    fin_cases i <;> norm_num at h ⊢
    · field_simp at h
      exact h
    · field_simp at h
      exact h

end MainTheory.TwoSpinorNormalization
