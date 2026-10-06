import MainTheory.Orbit30PrintedMoments
set_option autoImplicit false
set_option maxHeartbeats 10000000
namespace MainTheory.Orbit30ProbabilityLabels
open SixQubit.Orbit30
open MainTheory.Orbit30PrintedMoments
open scoped BigOperators
noncomputable section
def vertexIndex : Fin 5 → Fin 16 := ![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨4,by decide⟩,⟨8,by decide⟩]
def edgeIndex : Fin 10 → Fin 16 := ![⟨14,by decide⟩,⟨13,by decide⟩,⟨11,by decide⟩,⟨7,by decide⟩,⟨12,by decide⟩,⟨10,by decide⟩,⟨6,by decide⟩,⟨9,by decide⟩,⟨5,by decide⟩,⟨3,by decide⟩]
def endpoints : Fin 10 → Fin 5 × Fin 5 := ![(⟨0,by decide⟩,⟨1,by decide⟩),(⟨0,by decide⟩,⟨2,by decide⟩),(⟨0,by decide⟩,⟨3,by decide⟩),(⟨0,by decide⟩,⟨4,by decide⟩),(⟨1,by decide⟩,⟨2,by decide⟩),(⟨1,by decide⟩,⟨3,by decide⟩),(⟨1,by decide⟩,⟨4,by decide⟩),(⟨2,by decide⟩,⟨3,by decide⟩),(⟨2,by decide⟩,⟨4,by decide⟩),(⟨3,by decide⟩,⟨4,by decide⟩)]
def coordQ (i : Fin 16) (j : Fin 6) : ℚ := if bottom i j then 1 else 0
def firstFourQ (i : Fin 16) : ℚ := coordQ i 0+coordQ i 1+coordQ i 2+coordQ i 3
def starIndicatorQ (i : Fin 16) : ℚ := if i.val=15 then 1 else 0
def vertexIndicatorQ (v : Fin 5) (i : Fin 16) : ℚ := if vertexIndex v=i then 1 else 0
def degreeIndicatorQ (v : Fin 5) (i : Fin 16) : ℚ :=
  ∑ e : Fin 10,if (endpoints e).1=v ∨ (endpoints e).2=v then
    (if edgeIndex e=i then 1 else 0) else 0
theorem literal_pointwise_identities :
    (∀ i,starIndicatorQ i=firstFourQ i/4-coordQ i 4/2-coordQ i 5/4) ∧
    (∀ i,degreeIndicatorQ 0 i-vertexIndicatorQ 0 i=
      -1+firstFourQ i/4+coordQ i 4/2+3*coordQ i 5/4) ∧
    (∀ v : Fin 4,∀ i,degreeIndicatorQ ⟨v.val+1,by omega⟩ i-
      vertexIndicatorQ ⟨v.val+1,by omega⟩ i=
      firstFourQ i/4-coordQ i ⟨3-v.val,by omega⟩+coordQ i 4/2-coordQ i 5/4) := by decide +kernel
def pointMass (p : Fin 16 → ℝ) : Fin 5 → ℝ := fun i => p (vertexIndex i)
def edgeMass (p : Fin 16 → ℝ) : Fin 10 → ℝ := fun i => p (edgeIndex i)
def degreeMass (p : Fin 16 → ℝ) : Fin 5 → ℝ := ![p ⟨14,by decide⟩ + p ⟨13,by decide⟩ + p ⟨11,by decide⟩ + p ⟨7,by decide⟩,p ⟨14,by decide⟩ + p ⟨12,by decide⟩ + p ⟨10,by decide⟩ + p ⟨6,by decide⟩,p ⟨13,by decide⟩ + p ⟨12,by decide⟩ + p ⟨9,by decide⟩ + p ⟨5,by decide⟩,p ⟨11,by decide⟩ + p ⟨10,by decide⟩ + p ⟨9,by decide⟩ + p ⟨3,by decide⟩,p ⟨7,by decide⟩ + p ⟨6,by decide⟩ + p ⟨5,by decide⟩ + p ⟨3,by decide⟩]
theorem literal_degree_sum (p : Fin 16 → ℝ) (v : Fin 5) :
    degreeMass p v=∑ e : Fin 10,if (endpoints e).1=v ∨ (endpoints e).2=v then edgeMass p e else 0 := by
  fin_cases v <;> norm_num [degreeMass,edgeMass,edgeIndex,endpoints,Fin.sum_univ_succ,Fin.succ] <;> ring
theorem actual_probabilities (p t : Fin 16 → ℝ) (hm : Moment p t) :
    p ⟨15,by decide⟩=1/8 ∧
    (∀ v,degreeMass p v=pointMass p v+1/8) ∧
    (∑ v,pointMass p v)=3/8 ∧ (∑ e,edgeMass p e)=1/2 := by
  have he := hm.endpoints
  refine ⟨he.1,?_,?_,?_⟩
  · intro v
    fin_cases v
    · exact he.2.2.1
    · exact he.2.2.2.1
    · exact he.2.2.2.2.1
    · exact he.2.2.2.2.2.1
    · exact he.2.2.2.2.2.2.1
  · have h := he.2.2.2.2.2.2.2.1
    change p (0 : Fin 16)+p (1 : Fin 16)+p ⟨2,by decide⟩+p ⟨4,by decide⟩+p ⟨8,by decide⟩=3/8 at h
    norm_num [pointMass,vertexIndex,Fin.sum_univ_succ,Fin.succ]
    convert h using 1
    ring
  · have h := he.2.2.2.2.2.2.2.2
    norm_num [edgeMass,edgeIndex,Fin.sum_univ_succ,Fin.succ]
    convert h using 1
    ring
theorem physical_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3) :
    bottomProbability c ⟨15,by decide⟩=1/8 ∧
    (∀ v,degreeMass (bottomProbability c) v=pointMass (bottomProbability c) v+1/8) ∧
    (∑ v,pointMass (bottomProbability c) v)=3/8 ∧
    (∑ e,edgeMass (bottomProbability c) e)=1/2 :=
  actual_probabilities _ _ (physical_moments c d hc hd hnc hnd hkl)
end
end MainTheory.Orbit30ProbabilityLabels
