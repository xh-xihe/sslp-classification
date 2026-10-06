import SixQubit.CodeOrbit28
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit28PrintedProbabilities
open SixQubit.Orbit28
open scoped BigOperators
noncomputable section
def bottom : Fin 16 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15]
def top : Fin 16 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15]
def bottomProbability : Fin 16 → ℝ := ![3/8,0,0,0,0,0,0,1/8,0,0,0,1/8,0,1/8,1/8,1/8]
def topProbability : Fin 16 → ℝ := ![1/8,1/8,1/8,0,1/8,0,0,0,1/8,0,0,0,0,0,0,3/8]
def VectorMoments (q r : Fin 16 → ℝ) : Prop := MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (q ⟨12,by decide⟩) (q ⟨13,by decide⟩) (q ⟨14,by decide⟩) (q ⟨15,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) (r ⟨12,by decide⟩) (r ⟨13,by decide⟩) (r ⟨14,by decide⟩) (r ⟨15,by decide⟩)

theorem complete_normal (q r : Fin 16 → ℝ) (hm : VectorMoments q r) :
    q=bottomProbability ∧ r=topProbability := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (q ⟨12,by decide⟩) (q ⟨13,by decide⟩) (q ⟨14,by decide⟩) (q ⟨15,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) (r ⟨12,by decide⟩) (r ⟨13,by decide⟩) (r ⟨14,by decide⟩) (r ⟨15,by decide⟩) at hm
  obtain ⟨n0,n1,m1,m2,m3,m4,m5,m6,c12,c13,c14,c15,c16,c23,c24,c25,c26,c34,c35,c36,c45,c46,c56,nq0,nq1,nq2,nq3,nq4,nq5,nq6,nq7,nq8,nq9,nq10,nq11,nq12,nq13,nq14,nq15,nr0,nr1,nr2,nr3,nr4,nr5,nr6,nr7,nr8,nr9,nr10,nr11,nr12,nr13,nr14,nr15⟩ := hm
  constructor
  · ext i
    fin_cases i
    · change q ⟨0,by decide⟩=3/8
      linarith
    · change q ⟨1,by decide⟩=0
      linarith
    · change q ⟨2,by decide⟩=0
      linarith
    · change q ⟨3,by decide⟩=0
      linarith
    · change q ⟨4,by decide⟩=0
      linarith
    · change q ⟨5,by decide⟩=0
      linarith
    · change q ⟨6,by decide⟩=0
      linarith
    · change q ⟨7,by decide⟩=1/8
      linarith
    · change q ⟨8,by decide⟩=0
      linarith
    · change q ⟨9,by decide⟩=0
      linarith
    · change q ⟨10,by decide⟩=0
      linarith
    · change q ⟨11,by decide⟩=1/8
      linarith
    · change q ⟨12,by decide⟩=0
      linarith
    · change q ⟨13,by decide⟩=1/8
      linarith
    · change q ⟨14,by decide⟩=1/8
      linarith
    · change q ⟨15,by decide⟩=1/8
      linarith
  · ext i
    fin_cases i
    · change r ⟨0,by decide⟩=1/8
      linarith
    · change r ⟨1,by decide⟩=1/8
      linarith
    · change r ⟨2,by decide⟩=1/8
      linarith
    · change r ⟨3,by decide⟩=0
      linarith
    · change r ⟨4,by decide⟩=1/8
      linarith
    · change r ⟨5,by decide⟩=0
      linarith
    · change r ⟨6,by decide⟩=0
      linarith
    · change r ⟨7,by decide⟩=0
      linarith
    · change r ⟨8,by decide⟩=1/8
      linarith
    · change r ⟨9,by decide⟩=0
      linarith
    · change r ⟨10,by decide⟩=0
      linarith
    · change r ⟨11,by decide⟩=0
      linarith
    · change r ⟨12,by decide⟩=0
      linarith
    · change r ⟨13,by decide⟩=0
      linarith
    · change r ⟨14,by decide⟩=0
      linarith
    · change r ⟨15,by decide⟩=3/8
      linarith

theorem physical_normal (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (fun i => Complex.normSq (c (bottom i)))=bottomProbability ∧
    (fun i => Complex.normSq (d (top i)))=topProbability := by
  apply complete_normal
  exact SixQubit.Orbit28.moments c d hc hd hnc hnd hkl

def bottomActive : Finset (SS.BitString 6) := {y0,y7,y11,y13,y14,y15}
def topActive : Finset (SS.BitString 6) := {z0,z1,z2,z4,z8,z15}

theorem literal_supports : bottomActive.card=6 ∧ topActive.card=6 ∧
    (∀ i : Fin 16,bottomProbability i≠0 ↔ bottom i∈bottomActive) ∧
    (∀ i : Fin 16,topProbability i≠0 ↔ top i∈topActive) := by
  refine ⟨by decide +kernel,by decide +kernel,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [bottomProbability,bottom,bottomActive] <;> decide +kernel
  · intro i
    fin_cases i <;> norm_num [topProbability,top,topActive] <;> decide +kernel
theorem bottom_full : ∀ x : SS.BitString 6,x∈S0 ↔ ∃ i,bottom i=x := by decide +kernel
theorem top_full : ∀ x : SS.BitString 6,x∈S1 ↔ ∃ i,top i=x := by decide +kernel

theorem physical_supports (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ x,c x≠0 ↔ x∈bottomActive) ∧ (∀ x,d x≠0 ↔ x∈topActive) := by
  obtain ⟨hq,hr⟩ := physical_normal c d hc hd hnc hnd hkl
  constructor
  · intro x
    by_cases hs : x∈S0
    · obtain ⟨i,rfl⟩ := (bottom_full x).mp hs
      have he := congrFun hq i
      simp only [ne_eq,← Complex.normSq_eq_zero,he]
      exact literal_supports.2.2.1 i
    · have hz := hc x hs
      have ha : bottomActive⊆S0 := by decide +kernel
      simp only [hz,ne_eq,not_true_eq_false,false_iff]
      exact fun h => hs (ha h)
  · intro x
    by_cases hs : x∈S1
    · obtain ⟨i,rfl⟩ := (top_full x).mp hs
      have he := congrFun hr i
      simp only [ne_eq,← Complex.normSq_eq_zero,he]
      exact literal_supports.2.2.2 i
    · have hz := hd x hs
      have ha : topActive⊆S1 := by decide +kernel
      simp only [hz,ne_eq,not_true_eq_false,false_iff]
      exact fun h => hs (ha h)
end
end MainTheory.Orbit28PrintedProbabilities
