import MainTheory.WithinSectorRationalization
import MainTheory.PhaseSectorBridge

set_option autoImplicit false

namespace MainTheory.WithinSectorCodeAction

open MainTheory.WithinSectorRationalization MainTheory.PhaseSectorFull
open MainTheory.PhaseSectorBridge MainTheory.FiniteLift MainTheory.RealGate

noncomputable section

variable {n t K d : ℕ} {theta : Fin n → ℝ}

def commonShift (D : SectorDecomposition n t theta) (v : Fin n → ℝ) : ℝ :=
  ∑ j,(v j-theta j)*sectorMean D (baseSector D) j

theorem sector_action (D : SectorDecomposition n t theta) (hZ : ZDetects D)
    (v : Fin n → ℝ)
    (hv : ((rows D).map (algebraMap ℚ ℝ)).mulVec v=fun r => (rhs D r : ℝ))
    (u : D.Index) :
    realGateEnd v (D.vec u)=phaseExp (commonShift D v) • realGateEnd theta (D.vec u) := by
  funext x
  by_cases hx : D.vec u x=0
  · simp [realGateEnd_apply,realGate,hx]
  have h := common_phase_shift D hZ v hv u.1 ⟨x,vec_ne_zero_mem_sectorSupport D u x hx⟩
  rw [angle_sub] at h
  have he : angle v x=commonShift D v+angle theta x := by unfold commonShift; linarith
  simp only [realGateEnd_apply,realGate,he,phaseExp,Complex.ofReal_add,mul_add,
    Complex.exp_add,Pi.smul_apply,smul_eq_mul]
  ring

theorem code_action (C : MainTheory.CodeSpec.ExactCode n K d)
    (R : LogicalSectorResolution C theta) (hZ : ZDetects R.sectors) (v : Fin n → ℝ)
    (hv : ((rows R.sectors).map (algebraMap ℚ ℝ)).mulVec v=fun r => (rhs R.sectors r : ℝ))
    (f : SS.State n ℂ) (hf : f ∈ MainTheory.CodeSpec.codeSpan C.frame) :
    realGateEnd v f=phaseExp (commonShift R.sectors v) • realGateEnd theta f := by
  rw [R.link.span_eq] at hf
  refine Submodule.span_induction
    (p := fun f _ => realGateEnd v f=phaseExp (commonShift R.sectors v) • realGateEnd theta f)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨k,rfl⟩
    exact sector_action R.sectors hZ v hv (R.link.reindex k)
  · simp only [map_zero,smul_zero]
  · intro f g _ _ h1 h2
    simp only [map_add,h1,h2,smul_add]
  · intro a f _ h
    rw [map_smul,map_smul,h,smul_comm a]

theorem exists_rational_code_action (C : MainTheory.CodeSpec.ExactCode n K d)
    (R : LogicalSectorResolution C theta) (hZ : ZDetects R.sectors) :
    ∃ v : Fin n → ℚ,(rows R.sectors).mulVec v=rhs R.sectors ∧
      ∀ f ∈ MainTheory.CodeSpec.codeSpan C.frame,
        realGateEnd (fun j => (v j : ℝ)) f=
          phaseExp (commonShift R.sectors (fun j => (v j : ℝ))) • realGateEnd theta f := by
  obtain ⟨v,hv⟩ := exists_rational_solution R.sectors
  exact ⟨v,hv,code_action C R hZ _ (rational_solution_real R.sectors v hv)⟩

end

end MainTheory.WithinSectorCodeAction
