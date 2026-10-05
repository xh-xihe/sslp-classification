import MainTheory.Orbit33PrintedBlocks
import MainTheory.Orbit33ScalarReflection

/-! The complete printed character equations for an arbitrary complex 2x2 F.
The equations are derived from actual physical distance, support and norms.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit33PhysicalReflection
open MainTheory.Orbit33PrintedBlocks
open scoped BigOperators Matrix
noncomputable section

theorem R_cast : ∀ i, MainTheory.Orbit33ScalarReflection.R i=(R i : ℂ) := by
  intro i
  fin_cases i <;> norm_num [MainTheory.Orbit33ScalarReflection.R,R]

theorem physical_scalar_reflection (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3)
    (F : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) :
    evaluation F (CBlock c i)+evaluation F (DBlock d i)=
      2*MainTheory.Orbit33ScalarReflection.R i*(∑ j, evaluation F (CBlock c j)) := by
  rw [R_cast]
  exact scalar_reflection_of_matrix c d (physical_norms_and_reflection c d hc hd hnc hnd hkl).2 F i

theorem physical_character_reflection (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3)
    (F : Matrix (Fin 2) (Fin 2) ℂ) :
    (fun i => evaluation F (CBlock c i))=
      (MainTheory.Orbit33ScalarReflection.C⁻¹*MainTheory.Orbit33ScalarReflection.J*
        MainTheory.Orbit33ScalarReflection.C).mulVec (fun i => evaluation F (DBlock d i)) := by
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,MainTheory.Orbit33ScalarReflection.inverse]
  exact MainTheory.Orbit33ScalarReflection.inverse_character_rows _ _
    (physical_scalar_reflection c d hc hd hnc hnd hkl F)

theorem physical_common_reduced_state (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    rho c=(∑ i, outer (DBlock d i)) := by
  have hm := (physical_norms_and_reflection c d hc hd hnc hnd hkl).2
  ext r s
  have h0 := congrFun (congrFun (hm ⟨0,by decide⟩) r) s
  have h1 := congrFun (congrFun (hm ⟨1,by decide⟩) r) s
  have h2 := congrFun (congrFun (hm ⟨2,by decide⟩) r) s
  have h3 := congrFun (congrFun (hm ⟨3,by decide⟩) r) s
  have h4 := congrFun (congrFun (hm ⟨4,by decide⟩) r) s
  have h5 := congrFun (congrFun (hm ⟨5,by decide⟩) r) s
  norm_num [rho,R,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2 h3 h4 h5 ⊢
  linear_combination -(h0+h1+h2+h3+h4+h5)

end
end MainTheory.Orbit33PhysicalReflection
