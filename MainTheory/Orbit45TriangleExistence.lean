import MainTheory.Orbit45PrintedEnumerator
import MainTheory.Orbit45PrintedAttainment

/-! Every printed probability triple admits unit phases closing its vector
triangle, including the three boundary triples. The phase construction is
explicit and uses ordinary real square-root algebra. -/
set_option autoImplicit false
namespace MainTheory.Orbit45TriangleExistence
noncomputable section

theorem domain_phases (b g s : ℝ) (H : Orbit45TrianglePolynomial.Domain b g s) :
    ∃ xi eta : ℂ, Orbit45PrintedAttainment.Triangle b g s xi eta := by
  by_cases hz : b*g*s=0
  · rcases Orbit45PrintedEnumerator.boundary_permutations b g s H hz with
      (⟨hb,hg,hs⟩ | ⟨hb,hg,hs⟩ | ⟨hb,hg,hs⟩)
    · refine ⟨1,-1,?_⟩
      constructor <;> norm_num [hb,hg,hs,Complex.normSq_apply]
    · refine ⟨-1,1,?_⟩
      constructor <;> norm_num [hb,hg,hs,Complex.normSq_apply]
    · refine ⟨1,-1,?_⟩
      constructor <;> norm_num [hb,hg,hs,Complex.normSq_apply]
  have b0 : b ≠ 0 := by intro he; simp [he] at hz
  have g0 : g ≠ 0 := by intro he; simp [he] at hz
  have s0 : s ≠ 0 := by intro he; simp [he] at hz
  have bp : 0<b := lt_of_le_of_ne H.beta_nonneg (Ne.symm b0)
  have gp : 0<g := lt_of_le_of_ne H.gamma_nonneg (Ne.symm g0)
  have sp : 0<s := lt_of_le_of_ne H.sigma_nonneg (Ne.symm s0)
  have hd : 0<2*b*s := by positivity
  have hg_le : g≤b+s := by linarith [H.sum,H.gamma_upper]
  have hb_le : b≤g+s := by linarith [H.sum,H.beta_upper]
  have hs_le : s≤b+g := by linarith [H.sum,H.sigma_upper]
  have hu : g^2-b^2-s^2≤2*b*s := by
    have he := mul_nonneg (sub_nonneg.mpr hg_le)
      (show 0≤b+s+g by linarith [H.beta_nonneg,H.gamma_nonneg,H.sigma_nonneg])
    nlinarith only [he]
  have hl : -2*b*s≤g^2-b^2-s^2 := by
    have he := mul_nonneg (show 0≤g-b+s by linarith only [hb_le])
      (show 0≤g+b-s by linarith only [hs_le])
    nlinarith only [he]
  let x : ℝ := (g^2-b^2-s^2)/(2*b*s)
  have hx1 : x≤1 := (div_le_iff₀ hd).mpr (by linarith only [hu])
  have hx0 : -1≤x := (le_div_iff₀ hd).mpr (by linarith only [hl])
  have hxx : 0≤1-x^2 := by nlinarith only [hx0,hx1]
  have hy := Real.sq_sqrt hxx
  have hangle : 2*b*s*x=g^2-b^2-s^2 := by
    dsimp [x]
    exact mul_div_cancel₀ _ (ne_of_gt hd)
  let xi : ℂ := (x : ℂ)+(Real.sqrt (1-x^2) : ℂ)*Complex.I
  let eta : ℂ := -((b : ℂ)*xi+(s : ℂ))/(g : ℂ)
  have hxi : Complex.normSq xi=1 := by
    norm_num [xi,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    nlinarith only [hy]
  have hnum : Complex.normSq ((b : ℂ)*xi+(s : ℂ))=g^2 := by
    norm_num [xi,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    nlinarith only [hy,hangle]
  have heta : Complex.normSq eta=1 := by
    dsimp [eta]
    rw [Complex.normSq_div,Complex.normSq_neg,hnum,Complex.normSq_ofReal]
    rw [← pow_two]
    exact div_self (pow_ne_zero _ g0)
  have ht : (b : ℂ)*xi+(g : ℂ)*eta+(s : ℂ)=0 := by
    have gc : (g : ℂ) ≠ 0 := by exact_mod_cast g0
    dsimp [eta]
    rw [mul_div_cancel₀ _ gc]
    ring
  exact ⟨xi,eta,H.beta_nonneg,H.gamma_nonneg,H.sigma_nonneg,H.sum,hxi,heta,ht⟩

theorem every_triple_attained (b g s : ℝ) (H : Orbit45TrianglePolynomial.Domain b g s) :
    ∃ xi eta : ℂ, Orbit45PrintedAttainment.Triangle b g s xi eta ∧
      SS.HasDistance ![Orbit45PrintedAttainment.canonical0 b g s xi eta,
        Orbit45PrintedAttainment.canonical1 b g s xi eta] 3 := by
  obtain ⟨xi,eta,ht⟩ := domain_phases b g s H
  exact ⟨xi,eta,ht,Orbit45PrintedAttainment.full_kl b g s xi eta ht⟩

theorem canonical_fullKL (b g s : ℝ) (xi eta : ℂ)
    (H : Orbit45PrintedAttainment.Triangle b g s xi eta) :
    Orbit45PhysicalGauge.FullKL (Orbit45PrintedAttainment.canonical0 b g s xi eta)
      (Orbit45PrintedAttainment.canonical1 b g s xi eta) where
  support0 := by
    intro x hx
    have ho : Orbit45PrintedAttainment.original0 b g s xi eta x=0 :=
      SixQubit.Orbit45Attain.cword_support _ _ _ _ _ _ _ _ _ _ x hx
    simp [Orbit45PrintedAttainment.canonical0,ClassificationLevels.diagonalAction,ho]
  support1 := by
    intro x hx
    have ho : Orbit45PrintedAttainment.original1 b g s xi eta x=0 :=
      SixQubit.Orbit45Attain.dword_support _ _ _ _ _ _ _ _ _ _ x hx
    simp [Orbit45PrintedAttainment.canonical1,ClassificationLevels.diagonalAction,ho]
  norm0 := (Orbit45PrintedAttainment.normalized b g s xi eta H).1
  norm1 := (Orbit45PrintedAttainment.normalized b g s xi eta H).2
  distance := Orbit45PrintedAttainment.full_kl b g s xi eta H

theorem every_triple_completion (b g s : ℝ) (H : Orbit45TrianglePolynomial.Domain b g s) :
    ∃ xi eta : ℂ, Orbit45PrintedAttainment.Triangle b g s xi eta ∧
      Orbit45PhysicalGauge.FullKL (Orbit45PrintedAttainment.canonical0 b g s xi eta)
        (Orbit45PrintedAttainment.canonical1 b g s xi eta) := by
  obtain ⟨xi,eta,ht⟩ := domain_phases b g s H
  exact ⟨xi,eta,ht,canonical_fullKL b g s xi eta ht⟩
end
end MainTheory.Orbit45TriangleExistence
