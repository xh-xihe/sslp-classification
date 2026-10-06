import MainTheory.Orbit30PhysicalRows
import MainTheory.PhysicalPhaseQuotients
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit30PhysicalPhases
open SixQubit.Orbit30
open MainTheory.Orbit30PrintedMoments MainTheory.Orbit30ProbabilityLabels
open MainTheory.Orbit30PhysicalRows
noncomputable section
def phase (c d : SS.State 6 ℂ) (i : Fin 16) : ℂ :=
  MainTheory.PhysicalPhaseQuotients.rho (c (bottom i)) (d (top (complementIndex i)))
theorem actual_equal_norms (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3)
    (i : Fin 16) : Complex.normSq (d (top (complementIndex i)))=Complex.normSq (c (bottom i)) :=
  congrFun (physical_normal c d hc hd hnc hnd hkl).1 i
theorem actual_unit_phase (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3)
    (i : Fin 16) (hi : c (bottom i)≠0) : Complex.normSq (phase c d i)=1 :=
  MainTheory.PhysicalPhaseQuotients.unit _ _ hi (actual_equal_norms c d hc hd hnc hnd hkl i)
theorem reciprocal_product (c d : SS.State 6 ℂ) (i j : Fin 16) (hj : c (bottom j)≠0) :
    star (c (bottom i))*d (top (complementIndex j))=
      phase c d j*star (c (bottom i)*c (bottom j)) := by
  dsimp [phase,MainTheory.PhysicalPhaseQuotients.rho]
  rw [map_mul]
  have hs : (starRingEnd ℂ) (c (bottom j))≠0 := star_ne_zero.2 hj
  field_simp [hs]
theorem actual_anchor_nonzero (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3) :
    c y15≠0 ∧ d z0≠0 := by
  have hp := (physical_probabilities c d hc hd hnc hnd hkl).1
  change Complex.normSq (c y15)=1/8 at hp
  have hq := actual_equal_norms c d hc hd hnc hnd hkl ⟨15,by decide⟩
  change Complex.normSq (d z0)=Complex.normSq (c y15) at hq
  constructor
  · intro h
    rw [h] at hp
    norm_num at hp
  · intro h
    rw [h,hp] at hq
    norm_num at hq
theorem actual_point_phase (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3)
    (i : Fin 5) (hi : pointC c i≠0) :
    phase c d (vertexIndex i)=-phase c d ⟨15,by decide⟩ := by
  have ha := (actual_anchor_nonzero c d hc hd hnc hnd hkl).1
  have hr := (physical_rows c d hc hd hkl).2.1 i
  have h := MainTheory.PhysicalPhaseQuotients.opposition (c y15) (d z0)
    (pointC c i) (pointV d i) ha hi hr
  change phase c d ⟨15,by decide⟩+phase c d (vertexIndex i)=0 at h
  linear_combination h
theorem actual_edge_phase (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3)
    (i j : Fin 5) (hij : i≠j) (hj : pointC c j≠0) (he : edgeC c i j≠0) :
    phase c d (edgeIndexMatrix i j)=-phase c d ⟨15,by decide⟩ := by
  have hr := (physical_rows c d hc hd hkl).1 i j hij
  have h := MainTheory.PhysicalPhaseQuotients.equality (pointC c j) (pointV d j)
    (edgeC c i j) (edgeV d i j) hj he (sub_eq_zero.mp hr)
  have hd' : MainTheory.PhysicalPhaseQuotients.rho (edgeC c i j) (edgeV d i j)=
      phase c d (edgeIndexMatrix i j) := by
    simp only [edgeC,edgeV,if_neg hij,phase]
  rw [hd'] at h
  exact h.symm.trans (actual_point_phase c d hc hd hnc hnd hkl j hj)
end
end MainTheory.Orbit30PhysicalPhases
