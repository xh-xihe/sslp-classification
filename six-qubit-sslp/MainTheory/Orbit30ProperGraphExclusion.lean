import MainTheory.Orbit30GraphRelabel
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30ProperGraphExclusion
open MainTheory.Orbit30GraphClassification MainTheory.Orbit30GraphRelabel
open MainTheory.Orbit30ProperGraphTables
noncomputable section

theorem literal_endpoints : ∀ e : Fin 10,
    (endpoints e).1≠(endpoints e).2 ∧ edgeIndex (endpoints e).1 (endpoints e).2=e := by
  decide +kernel

theorem representative_no_go (r : Fin 10) (z : Fin 10 → ℂ)
    (hm : Missing z (representative r)) (hh : ∀ i,hafnian z i=0) : False := by
  fin_cases r
  · exact binomial3 z hm hh
  · exact binomial2 z hm hh
  · exact monomial5 z hm (hh ⟨0,by decide⟩)
  · exact binomial1 z hm hh
  · exact monomial4 z hm (hh ⟨2,by decide⟩)
  · exact monomial3 z hm (hh ⟨0,by decide⟩)
  · exact binomial0 z hm hh
  · exact monomial2 z hm (hh ⟨0,by decide⟩)
  · exact monomial1 z hm (hh ⟨0,by decide⟩)
  · exact monomial0 z hm (hh ⟨0,by decide⟩)

theorem relabeled_missing (z : Fin 10 → ℂ) (m : Fin 1024)
    (hm : Admissible m) (hz : Missing z m) :
    Missing (fun e => z (relabelEdge
      (Equiv.ofBijective (relabelWitness m) (exhaustive_relabeling m hm).1).symm e))
      (representative (typeWitness m)) := by
  let p := Equiv.ofBijective (relabelWitness m) (exhaustive_relabeling m hm).1
  intro e
  have hab := (literal_endpoints e).1
  have hfab := p.symm.injective.ne hab
  have he := (literal_endpoints e).2
  have hr := (exhaustive_relabeling m hm).2
    (p.symm (endpoints e).1) (p.symm (endpoints e).2)
  have hp1 : relabelWitness m (p.symm (endpoints e).1)=(endpoints e).1 := p.apply_symm_apply _
  have hp2 : relabelWitness m (p.symm (endpoints e).2)=(endpoints e).2 := p.apply_symm_apply _
  rw [hp1,hp2] at hr
  have hbits : Nat.testBit m.val (relabelEdge p.symm e).val=
      Nat.testBit (representative (typeWitness m)).val e.val := by
    simpa only [missing,if_neg hfab,if_neg hab,relabelEdge,he] using hr
  change z (relabelEdge p.symm e)=0 ↔ _
  rw [← hbits]
  exact hz (relabelEdge p.symm e)

theorem proper_no_go (z : Fin 10 → ℂ) (m : Fin 1024)
    (hm : Admissible m) (hz : Missing z m) (hh : ∀ i,hafnian z i=0) : False := by
  let p := Equiv.ofBijective (relabelWitness m) (exhaustive_relabeling m hm).1
  apply representative_no_go (typeWitness m) (fun e => z (relabelEdge p.symm e))
  · exact relabeled_missing z m hm hz
  · intro i
    rw [hafnian_relabel z p.symm p.symm.bijective]
    exact hh (p.symm i)
end
end MainTheory.Orbit30ProperGraphExclusion
