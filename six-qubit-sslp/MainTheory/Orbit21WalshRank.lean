import MainTheory.Orbit21WalshFace

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.Orbit21WalshRank

open MainTheory.Orbit21WalshFace

noncomputable def parameters : (Fin 2 → ℂ) ≃ₗ[ℂ] LinearMap.ker W.mulVecLin where
  toFun p := ⟨kernelPattern (p 0) (p 1),by
    change W.mulVec (kernelPattern (p 0) (p 1))=0
    apply (kernel_iff _).2
    rfl⟩
  invFun z := ![z.1 2,z.1 0]
  left_inv p := by
    funext i
    fin_cases i <;> rfl
  right_inv z := by
    apply Subtype.ext
    exact ((kernel_iff z.1).1 z.2).symm
  map_add' p q := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [kernelPattern,add_comm]
  map_smul' a p := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [kernelPattern]

theorem kernel_dimension : Module.finrank ℂ (LinearMap.ker W.mulVecLin)=2 := by
  simpa using (LinearEquiv.finrank_eq parameters).symm

theorem rank_six : W.rank=6 := by
  have h := LinearMap.finrank_range_add_finrank_ker W.mulVecLin
  rw [kernel_dimension] at h
  change W.rank+2=Module.finrank ℂ (Fin 8 → ℂ) at h
  norm_num at h
  omega

end MainTheory.Orbit21WalshRank
