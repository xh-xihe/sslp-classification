import MainTheory.Orbit51PrintedRows
import MainTheory.PhysicalPhaseQuotients
import MainTheory.Orbit49PrintedAlgebra

/-! Literal parameter pinning and boundary-inclusive phase synchronization
for orbit 51. Every complex division carries its nonzero hypothesis. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit51PrintedAlgebra
open MainTheory.OrderThreePrintedMoments.Orbit51
noncomputable section

def C (c : SS.State 6 ℂ) (i : Fin 10) := c (bottom i)
def D (d : SS.State 6 ℂ) (i : Fin 10) := d (top i)
def rho (c d : Fin 10 → ℂ) (i : Fin 10) := MainTheory.PhysicalPhaseQuotients.rho (c i) (d i)
def fixedIndices : Finset (Fin 10) := {0,1,⟨2,by decide⟩,⟨3,by decide⟩,⟨8,by decide⟩,⟨9,by decide⟩}
def fixedProbability (i : Fin 10) : ℝ := if i.val < 4 then 1/12 else 1/6
def KernelRows (c d : Fin 10 → ℂ) : Prop :=
  (star (c 0)*d ⟨9,by decide⟩=star (c ⟨9,by decide⟩)*d 0 ∧
   star (c 1)*d ⟨8,by decide⟩=star (c ⟨8,by decide⟩)*d 1 ∧
   star (c 0)*d ⟨9,by decide⟩+star (c 1)*d ⟨8,by decide⟩=0) ∧
  (star (c ⟨2,by decide⟩)*d ⟨9,by decide⟩=star (c ⟨9,by decide⟩)*d ⟨2,by decide⟩ ∧
   star (c ⟨3,by decide⟩)*d ⟨8,by decide⟩=star (c ⟨8,by decide⟩)*d ⟨3,by decide⟩ ∧
   star (c ⟨2,by decide⟩)*d ⟨9,by decide⟩+star (c ⟨3,by decide⟩)*d ⟨8,by decide⟩=0)
def SyncRows (c d : Fin 10 → ℂ) : Prop :=
  (star (c ⟨8,by decide⟩)*d ⟨6,by decide⟩+star (c ⟨6,by decide⟩)*d ⟨8,by decide⟩=0 ∧
   star (c ⟨9,by decide⟩)*d ⟨7,by decide⟩+star (c ⟨7,by decide⟩)*d ⟨9,by decide⟩=0) ∧
  (star (c ⟨9,by decide⟩)*d ⟨6,by decide⟩+star (c ⟨6,by decide⟩)*d ⟨9,by decide⟩=0 ∧
   star (c ⟨8,by decide⟩)*d ⟨7,by decide⟩+star (c ⟨7,by decide⟩)*d ⟨8,by decide⟩=0)

theorem linear_pin (b g : ℝ)
    (h1 : g*(b+g)=(1/6-g)*(1/3-b-g))
    (h2 : b*(b+g)=(1/6-b)*(1/3-b-g)) : 3*b+9*g=1 ∧ 9*b+3*g=1 := by
  constructor
  · linear_combination 18*h1
  · linear_combination 18*h2

theorem pin_parameters (b g : ℝ)
    (h1 : g*(b+g)=(1/6-g)*(1/3-b-g))
    (h2 : b*(b+g)=(1/6-b)*(1/3-b-g)) : b=1/12 ∧ g=1/12 := by
  obtain ⟨e1,e2⟩ := linear_pin b g h1 h2
  constructor <;> linarith only [e1,e2]

theorem kernel_norm_equalities (c d : Fin 10 → ℂ) (hr : KernelRows c d) :
    Complex.normSq (c 1)*Complex.normSq (d ⟨8,by decide⟩)=
      Complex.normSq (c 0)*Complex.normSq (d ⟨9,by decide⟩) ∧
    Complex.normSq (c ⟨3,by decide⟩)*Complex.normSq (d ⟨8,by decide⟩)=
      Complex.normSq (c ⟨2,by decide⟩)*Complex.normSq (d ⟨9,by decide⟩) := by
  constructor
  · simpa using (MainTheory.Orbit49PrintedAlgebra.norm_product
      (star (c 0)) (d ⟨9,by decide⟩) (star (c 1)) (d ⟨8,by decide⟩) hr.1.2.2).symm
  · simpa using (MainTheory.Orbit49PrintedAlgebra.norm_product
      (star (c ⟨2,by decide⟩)) (d ⟨9,by decide⟩)
      (star (c ⟨3,by decide⟩)) (d ⟨8,by decide⟩) hr.2.2.2).symm

theorem printed_pin_identities (c d : Fin 10 → ℂ)
    (hm : Moment (fun i => Complex.normSq (c i)) (fun i => Complex.normSq (d i)))
    (hr : KernelRows c d) :
    let b := Complex.normSq (c ⟨2,by decide⟩)
    let g := Complex.normSq (c 0)
    g*(b+g)=(1/6-g)*(1/3-b-g) ∧
    b*(b+g)=(1/6-b)*(1/3-b-g) := by
  obtain ⟨e1,e2⟩ := kernel_norm_equalities c d hr
  obtain ⟨hp,hq⟩ := normal_coordinates (fun i => Complex.normSq (c i))
    (fun i => Complex.normSq (d i)) hm
  have p1 := congrFun hp 1
  have p3 := congrFun hp ⟨3,by decide⟩
  have q8 := congrFun hq ⟨8,by decide⟩
  have q9 := congrFun hq ⟨9,by decide⟩
  change Complex.normSq (c 1)=1/6-Complex.normSq (c 0) at p1
  change Complex.normSq (c ⟨3,by decide⟩)=1/6-Complex.normSq (c ⟨2,by decide⟩) at p3
  change Complex.normSq (d ⟨8,by decide⟩)= -Complex.normSq (c ⟨2,by decide⟩)-Complex.normSq (c 0)+1/3 at q8
  change Complex.normSq (d ⟨9,by decide⟩)=Complex.normSq (c ⟨2,by decide⟩)+Complex.normSq (c 0) at q9
  rw [p1,q8,q9] at e1
  rw [p3,q8,q9] at e2
  constructor
  · linear_combination -e1
  · linear_combination -e2

theorem pinned_point (c d : Fin 10 → ℂ)
    (hm : Moment (fun i => Complex.normSq (c i)) (fun i => Complex.normSq (d i)))
    (hr : KernelRows c d) :
    (∀ i ∈ fixedIndices, Complex.normSq (c i)=fixedProbability i) ∧
    (∀ i, Complex.normSq (d i)=Complex.normSq (c i)) ∧
    Complex.normSq (c ⟨6,by decide⟩)+Complex.normSq (c ⟨7,by decide⟩)=1/6 := by
  obtain ⟨e1,e2⟩ := kernel_norm_equalities c d hr
  obtain ⟨h1,h2,_h8,_hd8,_hd9,_h67⟩ := hm.pinned e1 e2
  change Complex.normSq (c 1)=1/12 at h1
  change Complex.normSq (c ⟨2,by decide⟩)=1/12 at h2
  have h0 : Complex.normSq (c 0)=1/12 := by
    have he := consequence1 hm
    change Complex.normSq (c 1)=1/6-Complex.normSq (c 0) at he
    linarith only [he,h1]
  obtain ⟨hp,hq⟩ := normal_coordinates (fun i => Complex.normSq (c i))
    (fun i => Complex.normSq (d i)) hm
  refine ⟨?_,?_,?_⟩
  · intro i hi
    have he := congrFun hp i
    fin_cases i <;> norm_num [fixedIndices] at hi <;>
      norm_num [bottomProb,fixedProbability,h0,h2,Fin.succ] at he ⊢ <;> exact he
  · intro i
    exact (congrFun hq i).trans (congrFun hp i).symm
  · have e6 := congrFun hp ⟨6,by decide⟩
    have e7 := congrFun hp ⟨7,by decide⟩
    change Complex.normSq (c ⟨6,by decide⟩)=1/6-Complex.normSq (c ⟨4,by decide⟩) at e6
    change Complex.normSq (c ⟨7,by decide⟩)=Complex.normSq (c ⟨4,by decide⟩) at e7
    linear_combination e6+e7

theorem fixed_nonzero (c d : Fin 10 → ℂ)
    (hm : Moment (fun i => Complex.normSq (c i)) (fun i => Complex.normSq (d i)))
    (hr : KernelRows c d) (i : Fin 10) (hi : i ∈ fixedIndices) : c i≠0 ∧ d i≠0 := by
  have hp := pinned_point c d hm hr
  have hpos : 0 < Complex.normSq (c i) := by
    rw [hp.1 i hi]
    unfold fixedProbability
    split <;> norm_num
  exact ⟨Complex.normSq_pos.1 hpos,Complex.normSq_pos.1 (by rw [hp.2.1 i]; exact hpos)⟩

theorem partial_sync (c d : Fin 10 → ℂ)
    (hm : Moment (fun i => Complex.normSq (c i)) (fun i => Complex.normSq (d i)))
    (hr : KernelRows c d) :
    rho c d 0=rho c d ⟨9,by decide⟩ ∧ rho c d 1=rho c d ⟨8,by decide⟩ ∧
    rho c d ⟨2,by decide⟩=rho c d ⟨9,by decide⟩ ∧
    rho c d ⟨3,by decide⟩=rho c d ⟨8,by decide⟩ := by
  have hn (i : Fin 10) (hi : i ∈ fixedIndices) := (fixed_nonzero c d hm hr i hi).1
  refine ⟨?_,?_,?_,?_⟩
  · exact MainTheory.PhysicalPhaseQuotients.equality _ _ _ _
      (hn 0 (by decide)) (hn ⟨9,by decide⟩ (by decide)) hr.1.1
  · exact MainTheory.PhysicalPhaseQuotients.equality _ _ _ _
      (hn 1 (by decide)) (hn ⟨8,by decide⟩ (by decide)) hr.1.2.1
  · exact MainTheory.PhysicalPhaseQuotients.equality _ _ _ _
      (hn ⟨2,by decide⟩ (by decide)) (hn ⟨9,by decide⟩ (by decide)) hr.2.1
  · exact MainTheory.PhysicalPhaseQuotients.equality _ _ _ _
      (hn ⟨3,by decide⟩ (by decide)) (hn ⟨8,by decide⟩ (by decide)) hr.2.2.1

theorem boundary_active (c d : Fin 10 → ℂ)
    (hm : Moment (fun i => Complex.normSq (c i)) (fun i => Complex.normSq (d i)))
    (hr : KernelRows c d) : c ⟨6,by decide⟩≠0 ∨ c ⟨7,by decide⟩≠0 := by
  have hp := (pinned_point c d hm hr).2.2
  by_contra h
  push_neg at h
  rw [h.1,h.2,Complex.normSq_zero] at hp
  norm_num at hp

theorem anchor_sync (c d : Fin 10 → ℂ)
    (hm : Moment (fun i => Complex.normSq (c i)) (fun i => Complex.normSq (d i)))
    (hr : KernelRows c d) (hs : SyncRows c d) : rho c d ⟨8,by decide⟩=rho c d ⟨9,by decide⟩ := by
  have h8 := (fixed_nonzero c d hm hr ⟨8,by decide⟩ (by decide)).1
  have h9 := (fixed_nonzero c d hm hr ⟨9,by decide⟩ (by decide)).1
  rcases boundary_active c d hm hr with h6|h7
  · have e8 := MainTheory.PhysicalPhaseQuotients.opposition _ _ _ _ h8 h6 hs.1.1
    have e9 := MainTheory.PhysicalPhaseQuotients.opposition _ _ _ _ h9 h6 hs.2.1
    change rho c d ⟨8,by decide⟩+rho c d ⟨6,by decide⟩=0 at e8
    change rho c d ⟨9,by decide⟩+rho c d ⟨6,by decide⟩=0 at e9
    linear_combination e8-e9
  · have e8 := MainTheory.PhysicalPhaseQuotients.opposition _ _ _ _ h8 h7 hs.2.2
    have e9 := MainTheory.PhysicalPhaseQuotients.opposition _ _ _ _ h9 h7 hs.1.2
    change rho c d ⟨8,by decide⟩+rho c d ⟨7,by decide⟩=0 at e8
    change rho c d ⟨9,by decide⟩+rho c d ⟨7,by decide⟩=0 at e9
    linear_combination e8-e9

theorem full_sync (c d : Fin 10 → ℂ)
    (hm : Moment (fun i => Complex.normSq (c i)) (fun i => Complex.normSq (d i)))
    (hr : KernelRows c d) (hs : SyncRows c d) :
    ∀ i ∈ fixedIndices, rho c d i=rho c d ⟨8,by decide⟩ := by
  obtain ⟨h0,h1,h2,h3⟩ := partial_sync c d hm hr
  have h89 := anchor_sync c d hm hr hs
  intro i hi
  fin_cases i <;> norm_num [fixedIndices] at hi
  · exact h0.trans h89.symm
  · exact h1
  · exact h2.trans h89.symm
  · exact h3
  · rfl
  · exact h89.symm

end
end MainTheory.Orbit51PrintedAlgebra
