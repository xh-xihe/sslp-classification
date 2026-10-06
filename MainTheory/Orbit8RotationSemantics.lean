import MainTheory.Orbit8ExcitationRotation
import MainTheory.PairEmbeddedAction
import SixQubit.Orbit8Family

set_option autoImplicit false

namespace MainTheory.Orbit8RotationSemantics

open MainTheory.PairPartialTrace SixQubit.Orbit7DirectMarginal
open SixQubit.CodeEquiv SixQubit.Orbit8Family SixQubit.Realize

noncomputable def physicalRotation (C S : ℝ) : Matrix (SS.BitString 6) (SS.BitString 6) ℂ :=
  embed 3 (fun p q => MainTheory.Orbit8ExcitationRotation.rotation C S (p.2,p.1) (q.2,q.1))

theorem flip_moved : ∀ e : Env,
    SS.bxor (assemblePair 3 (1,0) e) flip40=assemblePair 3 (0,1) e := by decide

theorem flip_moved_left (e : Env) :
    SS.bxor flip40 (assemblePair 3 (1,0) e)=assemblePair 3 (0,1) e := by
  rw [SS.bxor_comm]
  exact flip_moved e

theorem assemble_four (p : Pair) (e : Env) :
    assemblePair 3 p e 4=finTwoEquiv p.2 := by rfl

theorem assemble_zero (p : Pair) (e : Env) :
    assemblePair 3 p e 0=finTwoEquiv p.1 := by rfl

theorem action_fixed (C S : ℝ) (f : SS.State 6 ℂ)
    (hf : ∀ x,x 4=false → f x=0) (x : SS.BitString 6) :
    (physicalRotation C S).mulVec f x=
      if x 4 then (if x 0 then f x else (C : ℂ)*f x)
      else if x 0 then -(S : ℂ)*f (SS.bxor x flip40) else 0 := by
  obtain ⟨⟨⟨a,b⟩,e⟩,rfl⟩ := (assemblyEquiv 3).surjective x
  have h00 : f (assemblePair 3 (0,0) e)=0 := hf _ rfl
  have h10 : f (assemblePair 3 (1,0) e)=0 := hf _ rfl
  rw [assembly_apply,physicalRotation,MainTheory.PairEmbeddedAction.action_assembled]
  fin_cases a <;> fin_cases b <;>
    simp [MainTheory.Orbit8ExcitationRotation.rotation,Fintype.sum_prod_type,
      Fin.sum_univ_two,h00,h10,flip_moved_left,assemble_four,assemble_zero,finTwoEquiv]

theorem initial_fixed :
    (∀ x : SS.BitString 6,x 4=false → SixQubit.Orbit8Real.w0 x=0) ∧
    (∀ x : SS.BitString 6,x 4=false → SixQubit.Orbit8Real.w1 x=0) := by
  have h0 : ∀ x ∈ SixQubit.Orbit8Real.L0,x 4=true := by decide
  have h1 : ∀ x ∈ SixQubit.Orbit8Real.L1,x 4=true := by decide
  constructor
  · intro x hx
    apply SixQubit.Orbit8Real.w0_vanishes
    intro hm
    have h := h0 x hm
    simp [hx] at h
  · intro x hx
    apply SixQubit.Orbit8Real.w1_vanishes
    intro hm
    have h := h1 x hm
    simp [hx] at h

theorem actual_family (C S : ℝ) :
    (physicalRotation C S).mulVec SixQubit.Orbit8Real.w0=w0 C S ∧
    (physicalRotation C S).mulVec SixQubit.Orbit8Real.w1=w1 C S := by
  constructor
  · funext x
    rw [action_fixed C S _ initial_fixed.1]
    cases h4 : x 4 <;> cases h0 : x 0 <;>
      simp [w0,c0q,rotateCoeff,h4,h0,evalLin,LinZ.zero,SixQubit.Orbit8Real.w0,stC,
        toC_neg] <;> ring
  · funext x
    rw [action_fixed C S _ initial_fixed.2]
    cases h4 : x 4 <;> cases h0 : x 0 <;>
      simp [w1,c1q,rotateCoeff,h4,h0,evalLin,LinZ.zero,SixQubit.Orbit8Real.w1,stC,
        toC_neg] <;> ring

end MainTheory.Orbit8RotationSemantics
