import MainTheory.Orbit7EnumeratorDisplays

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.Orbit7WeightOneMass

open SixQubit.Orbit7Universal SS.MacWilliams

def onePaulis : Finset (SS.PauliString 6) := [tPX,tPY,tPZ].toFinset

@[simp] private theorem tPX_wt : tPX.wt = 1 := by decide
@[simp] private theorem tPY_wt : tPY.wt = 1 := by decide
@[simp] private theorem tPZ_wt : tPZ.wt = 1 := by decide
@[simp] private theorem tPXv_wt : ∀ v, (tPXv v).wt = 2 := by decide
@[simp] private theorem tPYv_wt : ∀ v, (tPYv v).wt = 2 := by decide
@[simp] private theorem tPZv_wt : ∀ v, (tPZv v).wt = 2 := by decide

theorem target_subset (s : Fin 5) : targetPaulis s ⊆ targetLowPaulis := by
  intro P h
  simp only [targetPaulis,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [targetLowPaulis]

theorem target_weight_one (s : Fin 5) (P : SS.PauliString 6)
    (h : P ∈ targetPaulis s) (hw : P.wt=1) : P ∈ onePaulis := by
  simp only [targetPaulis,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  all_goals simp at hw

theorem target_sum (s : Fin 5) (F : SS.PauliString 6 → ℝ) :
    (∑ P ∈ targetPaulis s,F P)=F tPX+F tPY+F tPZ+F (tPXv s)+F (tPYv s)+F (tPZv s) := by
  have hn : [tPX,tPY,tPZ,tPXv s,tPYv s,tPZv s].Nodup := by fin_cases s <;> decide
  simpa [targetPaulis,add_assoc] using List.sum_toFinset F hn

theorem low_sum (psi : Fin 2 → SS.State 6 ℂ) :
    (∑ P ∈ targetLowPaulis,Complex.normSq (trProj psi P))=Aco psi 1+Aco psi 2 := by
  have hd : Disjoint (Finset.univ.filter (fun P : SS.PauliString 6 => P.wt=1))
      (Finset.univ.filter (fun P : SS.PauliString 6 => P.wt=2)) := by
    rw [Finset.disjoint_left]
    intro P h1 h2
    have h1' := (Finset.mem_filter.mp h1).2
    have h2' := (Finset.mem_filter.mp h2).2
    omega
  exact Finset.sum_union hd

variable (c d : SS.State 6 ℂ)
  (hc : ∀ x,SS.weight uniformAv x ≠ 0 → c x=0)
  (hd : ∀ x,SS.weight uniformAv x ≠ 2 → d x=0)
  (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
  (hcode : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hcode

theorem trace_zero_outside (P : SS.PauliString 6) (hw : P.wt=1) (hp : P ∉ onePaulis) :
    trProj ![c,d] P=0 := by
  let ht := MainTheory.Orbit7StructuralDisplay.universal_target c d hc hd hnc hnd hcode
  let s := ht.choose
  let F := fun Q : SS.PauliString 6 => Complex.normSq (trProj ![c,d] Q)
  have htarget : (∑ Q ∈ targetPaulis s,F Q)=4 := by
    rw [target_sum]
    exact target_six_trace_sum c d hc hd hnc hnd hcode ht
  have hlow : (∑ Q ∈ targetLowPaulis,F Q)=4 := by
    rw [low_sum]
    have h := (MainTheory.Orbit7EnumeratorDisplays.line_identities c d hc hd hnc hnd hcode).1
    dsimp only [MainTheory.Orbit7EnumeratorDisplays.normalizedA] at h
    linarith
  have hsplit := Finset.sum_sdiff (f := F) (target_subset s)
  have hz : (∑ Q ∈ targetLowPaulis \ targetPaulis s,F Q)=0 := by linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun Q _ => Complex.normSq_nonneg (trProj ![c,d] Q))).mp hz
  have hP : P ∈ targetLowPaulis \ targetPaulis s := by
    apply Finset.mem_sdiff.mpr
    refine ⟨?_,fun h => hp (target_weight_one s P h hw)⟩
    simp [targetLowPaulis,hw]
  exact Complex.normSq_eq_zero.mp (hall P hP)

theorem Aco_one : Aco ![c,d] 1 = Complex.normSq (trProj ![c,d] tPX)+
    Complex.normSq (trProj ![c,d] tPY)+Complex.normSq (trProj ![c,d] tPZ) := by
  have hsub : onePaulis ⊆ Finset.univ.filter (fun P : SS.PauliString 6 => P.wt=1) := by
    intro P hP
    simp only [onePaulis,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hP
    rcases hP with rfl | rfl | rfl <;> simp
  have hsum := Finset.sum_subset (f := fun P => Complex.normSq (trProj ![c,d] P)) hsub
    (fun P hP hn => by
      change Complex.normSq (trProj ![c,d] P)=0
      rw [trace_zero_outside c d hc hd hnc hnd hcode P (Finset.mem_filter.mp hP).2 hn,
        Complex.normSq_zero])
  rw [Aco,← hsum]
  simpa [onePaulis,add_assoc] using List.sum_toFinset
    (fun P => Complex.normSq (trProj ![c,d] P))
    (show [tPX,tPY,tPZ].Nodup by decide)

end MainTheory.Orbit7WeightOneMass
