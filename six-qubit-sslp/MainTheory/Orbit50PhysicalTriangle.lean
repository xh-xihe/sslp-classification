import MainTheory.Orbit50PrintedRows
import MainTheory.PhysicalPhaseQuotients
import MainTheory.Orbit49PrintedAlgebra

/-! The literal orbit-50 phase triangle. Complementary top indexing is
explicitly reversed from the native order. Only one of indices 1,2,5 needs
to be active; no full-support assumption appears. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit50PhysicalTriangle
open scoped Matrix
open MainTheory.OrderThreePrintedMoments.Orbit50
noncomputable section
def C (c : SS.State 6 ℂ) (i : Fin 11) := c (bottom i)
def D (d : SS.State 6 ℂ) (i : Fin 11) := d (top (complementIndex i))
def rho (c d : SS.State 6 ℂ) (i : Fin 11) := MainTheory.PhysicalPhaseQuotients.rho (C c i) (D d i)
def activeIndices : Fin 3 → Fin 11 := ![1,⟨2,by decide⟩,⟨5,by decide⟩]

theorem complementary_index : complementIndex=
    ![⟨10,by decide⟩,⟨9,by decide⟩,⟨8,by decide⟩,⟨7,by decide⟩,⟨6,by decide⟩,
      ⟨5,by decide⟩,⟨4,by decide⟩,⟨3,by decide⟩,⟨2,by decide⟩,1,0] := by decide +kernel

theorem physical_masses (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit50.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit50.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (C c 0)=1/6 ∧ Complex.normSq (C c ⟨10,by decide⟩)=1/6 ∧
      Complex.normSq (C c 1)+Complex.normSq (C c ⟨2,by decide⟩)+Complex.normSq (C c ⟨5,by decide⟩)=1/3 :=
  key_masses (fun i => Complex.normSq (C c i)) (fun i => Complex.normSq (d (top i)))
    (SixQubit.Orbit50.moments c d hc hd hnc hnd hkl)

theorem physical_norm_matching (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit50.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit50.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ i, Complex.normSq (D d i)=Complex.normSq (C c i) := by
  obtain ⟨a,b,g,t,_h,hp,hq⟩ := physical_normal_form c d hc hd hnc hnd hkl
  have he : ∀ i, topProb a b g t (complementIndex i)=bottomProb a b g t i := by
    intro i
    rw [complementary_index]
    fin_cases i <;> norm_num [topProb,bottomProb,Fin.succ]
  intro i
  exact (congrFun hq (complementIndex i)).trans ((he i).trans (congrFun hp i).symm)

theorem physical_active (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit50.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit50.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∃ j : Fin 3, C c (activeIndices j)≠0 := by
  have hm := (physical_masses c d hc hd hnc hnd hkl).2.2
  by_contra h
  push_neg at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h ⟨2,by decide⟩
  change C c 1=0 at h0
  change C c ⟨2,by decide⟩=0 at h1
  change C c ⟨5,by decide⟩=0 at h2
  rw [h0,h1,h2,Complex.normSq_zero] at hm
  norm_num at hm

theorem physical_reciprocals (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit50.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit50.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c 0)*D d ⟨10,by decide⟩+star (C c ⟨10,by decide⟩)*D d 0=0 ∧
    (∀ j : Fin 3,
      star (C c 0)*D d (activeIndices j)+star (C c (activeIndices j))*D d 0=0 ∧
      star (C c (activeIndices j))*D d ⟨10,by decide⟩+star (C c ⟨10,by decide⟩)*D d (activeIndices j)=0) := by
  constructor
  · exact MainTheory.Orbit50PrintedRows.Row00.physical_reciprocal c d hc hd hkl
  · intro j
    fin_cases j
    · exact ⟨MainTheory.Orbit50PrintedRows.Row01.physical_reciprocal c d hc hd hkl,
             MainTheory.Orbit50PrintedRows.Row04.physical_reciprocal c d hc hd hkl⟩
    · exact ⟨MainTheory.Orbit50PrintedRows.Row02.physical_reciprocal c d hc hd hkl,
             MainTheory.Orbit50PrintedRows.Row05.physical_reciprocal c d hc hd hkl⟩
    · exact ⟨MainTheory.Orbit50PrintedRows.Row03.physical_reciprocal c d hc hd hkl,
             MainTheory.Orbit50PrintedRows.Row06.physical_reciprocal c d hc hd hkl⟩

theorem physical_triangle (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit50.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit50.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 3) (hj : C c (activeIndices j)≠0) :
    MainTheory.Orbit49PrintedAlgebra.triangleC *ᵥ ![rho c d 0,rho c d ⟨10,by decide⟩,rho c d (activeIndices j)]=0 ∧
    Complex.normSq (rho c d 0)=1 ∧ Complex.normSq (rho c d ⟨10,by decide⟩)=1 ∧
    Complex.normSq (rho c d (activeIndices j))=1 := by
  have hm := physical_masses c d hc hd hnc hnd hkl
  have h0 : C c 0≠0 := Complex.normSq_pos.1 (by rw [hm.1]; norm_num)
  have h10 : C c ⟨10,by decide⟩≠0 := Complex.normSq_pos.1 (by rw [hm.2.1]; norm_num)
  have he := physical_reciprocals c d hc hd hkl
  have r0 := MainTheory.PhysicalPhaseQuotients.opposition _ _ _ _ h0 h10 he.1
  have r1 := MainTheory.PhysicalPhaseQuotients.opposition _ _ _ _ h0 hj (he.2 j).1
  have r2 := MainTheory.PhysicalPhaseQuotients.opposition _ _ _ _ hj h10 (he.2 j).2
  refine ⟨(MainTheory.Orbit49PrintedAlgebra.triangle_equations _ _ _).2 ⟨r0,r1,?_⟩,?_,?_,?_⟩
  · simpa only [rho,add_comm] using r2
  · exact MainTheory.PhysicalPhaseQuotients.unit _ _ h0 (physical_norm_matching c d hc hd hnc hnd hkl 0)
  · exact MainTheory.PhysicalPhaseQuotients.unit _ _ h10 (physical_norm_matching c d hc hd hnc hnd hkl ⟨10,by decide⟩)
  · exact MainTheory.PhysicalPhaseQuotients.unit _ _ hj (physical_norm_matching c d hc hd hnc hnd hkl (activeIndices j))

theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit50.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit50.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  obtain ⟨j,hj⟩ := physical_active c d hc hd hnc hnd hkl
  obtain ⟨hm,hu,_,_⟩ := physical_triangle c d hc hd hnc hnd hkl j hj
  obtain ⟨r0,r1,r2⟩ := (MainTheory.Orbit49PrintedAlgebra.triangle_equations _ _ _).1 hm
  have hz : rho c d 0=0 := by linear_combination (1/2 : ℂ)*r0+(1/2 : ℂ)*r1-(1/2 : ℂ)*r2
  rw [hz,Complex.normSq_zero] at hu
  norm_num at hu
end
end MainTheory.Orbit50PhysicalTriangle
