import MainTheory.FiniteLift

/-! The within-sector, n-variable rationalization proof of main.tex (20260908).
No finite logical order and no auxiliary colour variables are hypotheses. -/

set_option autoImplicit false

namespace MainTheory.WithinSectorRationalization

open MainTheory.PhaseSectorFull MainTheory.FiniteLift MainTheory.RealGate

noncomputable section

variable {n t : ℕ} {theta : Fin n → ℝ}

theorem rational_algebra_map (q : ℚ) : (algebraMap ℚ ℝ) q=(q : ℝ) := rfl

def reference (D : SectorDecomposition n t theta) (a : Fin t) : SupportIndex D a :=
  ⟨Classical.choose (sectorSupport_nonempty D a),Classical.choose_spec (sectorSupport_nonempty D a)⟩

def rows (D : SectorDecomposition n t theta) : Matrix (Sigma (SupportIndex D)) (Fin n) ℚ :=
  fun r j => bitQ r.2.val j-bitQ (reference D r.1).val j

def rhsInt (D : SectorDecomposition n t theta) (r : Sigma (SupportIndex D)) : ℤ :=
  phaseInteger D r.1 r.2-phaseInteger D r.1 (reference D r.1)

def rhs (D : SectorDecomposition n t theta) (r : Sigma (SupportIndex D)) : ℚ := rhsInt D r

theorem row_dot (D : SectorDecomposition n t theta) (v : Fin n → ℝ)
    (r : Sigma (SupportIndex D)) :
    ((rows D).map (algebraMap ℚ ℝ)).mulVec v r=
      angle v r.2.val-angle v (reference D r.1).val := by
  simp only [Matrix.mulVec,dotProduct,Matrix.map_apply,rows,rational_algebra_map,Rat.cast_sub,
    bitQ_cast,angle,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold coordinate
  ring

theorem phase_difference (D : SectorDecomposition n t theta)
    (r : Sigma (SupportIndex D)) :
    angle theta r.2.val-angle theta (reference D r.1).val=(rhsInt D r : ℝ) := by
  have h1 := phaseInteger_spec D r.1 r.2
  have h2 := phaseInteger_spec D r.1 (reference D r.1)
  simp only [rhsInt,Int.cast_sub]
  linarith

theorem original_solution (D : SectorDecomposition n t theta) :
    ((rows D).map (algebraMap ℚ ℝ)).mulVec theta=fun r => (rhs D r : ℝ) := by
  funext r
  rw [row_dot,phase_difference]
  simp [rhs]

theorem exists_rational_solution (D : SectorDecomposition n t theta) :
    ∃ v : Fin n → ℚ,(rows D).mulVec v=rhs D := by
  exact MainTheory.Rationalize.exists_solution_of_exists_solution_ext
    (rows D) (rhs D) ⟨theta,original_solution D⟩

theorem rational_solution_real (D : SectorDecomposition n t theta) (v : Fin n → ℚ)
    (hv : (rows D).mulVec v=rhs D) :
    ((rows D).map (algebraMap ℚ ℝ)).mulVec (fun j => (v j : ℝ))=fun r => (rhs D r : ℝ) := by
  funext r
  have h := congrArg (fun q : ℚ => (q : ℝ)) (congrFun hv r)
  simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,rational_algebra_map,
    Rat.cast_sum,Rat.cast_mul] using h

theorem angle_sub (v w : Fin n → ℝ) (x : SS.BitString n) :
    angle (fun j => v j-w j) x=angle v x-angle w x := by
  simp only [angle,sub_mul,Finset.sum_sub_distrib]

theorem within_sector_constancy (D : SectorDecomposition n t theta) (v : Fin n → ℝ)
    (hv : ((rows D).map (algebraMap ℚ ℝ)).mulVec v=fun r => (rhs D r : ℝ))
    (a : Fin t) (x : SupportIndex D a) :
    angle (fun j => v j-theta j) x.val=
      angle (fun j => v j-theta j) (reference D a).val := by
  have h := congrFun hv ⟨a,x⟩
  rw [row_dot] at h
  have htheta := phase_difference D ⟨a,x⟩
  simp only [rhs,Rat.cast_intCast] at h
  simp only [angle_sub]
  linarith

theorem mean_angle (D : SectorDecomposition n t theta) (a : Fin t) (v : Fin n → ℝ) :
    (∑ x : SupportIndex D a,supportWeight D a x*angle v x.val)=
      ∑ j,v j*sectorMean D a j := by
  simp only [supportWeight]
  rw [sum_support_eq_sum]
  simp only [angle,sectorMean,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro x _
  unfold coordinate
  ring

theorem reference_mean (D : SectorDecomposition n t theta) (v : Fin n → ℝ)
    (hv : ((rows D).map (algebraMap ℚ ℝ)).mulVec v=fun r => (rhs D r : ℝ)) (a : Fin t) :
    angle (fun j => v j-theta j) (reference D a).val=
      ∑ j,(v j-theta j)*sectorMean D a j := by
  have h := mean_angle D a (fun j => v j-theta j)
  simp_rw [within_sector_constancy D v hv a] at h
  rw [← Finset.sum_mul,supportWeight_sum_eq_one,one_mul] at h
  exact h

theorem common_phase_shift (D : SectorDecomposition n t theta) (hZ : ZDetects D)
    (v : Fin n → ℝ)
    (hv : ((rows D).map (algebraMap ℚ ℝ)).mulVec v=fun r => (rhs D r : ℝ))
    (a : Fin t) (x : SupportIndex D a) :
    angle (fun j => v j-theta j) x.val=
      ∑ j,(v j-theta j)*sectorMean D (baseSector D) j := by
  rw [within_sector_constancy D v hv a,reference_mean D v hv a]
  simp_rw [sectorMean_eq_of_ZDetects D hZ a (baseSector D)]

theorem same_projective_action (D : SectorDecomposition n t theta) (hZ : ZDetects D)
    (v : Fin n → ℝ)
    (hv : ((rows D).map (algebraMap ℚ ℝ)).mulVec v=fun r => (rhs D r : ℝ)) :
    SameProjectiveSectorAction D v := by
  let shift : ℝ := ∑ j,(v j-theta j)*sectorMean D (baseSector D) j
  refine ⟨phaseExp shift,Complex.exp_ne_zero _,?_⟩
  intro u
  funext x
  by_cases hx : D.vec u x=0
  · simp [realGate,hx]
  have h := common_phase_shift D hZ v hv u.1 ⟨x,vec_ne_zero_mem_sectorSupport D u x hx⟩
  rw [angle_sub] at h
  have he : angle v x=shift+angle theta x := by dsimp [shift]; linarith
  simp only [realGate,he,phaseExp,Complex.ofReal_add,mul_add,Complex.exp_add]
  ring

theorem rational_replacement (D : SectorDecomposition n t theta) (hZ : ZDetects D) :
    ∃ v : Fin n → ℚ,(rows D).mulVec v=rhs D ∧
      SameProjectiveSectorAction D (fun j => (v j : ℝ)) := by
  obtain ⟨v,hv⟩ := exists_rational_solution D
  exact ⟨v,hv,same_projective_action D hZ _ (rational_solution_real D v hv)⟩

end

end MainTheory.WithinSectorRationalization
