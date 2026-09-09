import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderSevenWalshMatrix

def W : Matrix (Fin 3) (Fin 4) ℂ := fun i j =>
  if i=0 then 1 else if i=1 then (if j=1 ∨ j=3 then -1 else 1)
  else if j=2 ∨ j=3 then -1 else 1
def pattern (a : ℂ) : Fin 4 → ℂ := ![a,-a,-a,a]

theorem literal_matrix : W=!![1,1,1,1;1,-1,1,-1;1,1,-1,-1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [W] <;> decide

theorem kernel_iff (z : Fin 4 → ℂ) : W.mulVec z=0 ↔ z=pattern (z 0) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h ((0 : Fin 1).succ.succ)
    norm_num [W,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1 h2
    change z 0+(z 1+(z 2+z 3))=0 at h0
    change z 0+(-z 1+(z 2+ -z 3))=0 at h1
    change z 0+(z 1+(-z 2+ -z 3))=0 at h2
    funext i
    fin_cases i
    · rfl
    · change z 1= -z 0
      linear_combination (h0+h2)/2
    · change z 2= -z 0
      linear_combination (h0+h1)/2
    · change z 3=z 0
      linear_combination -(h1+h2)/2
  · intro h
    rw [h]
    ext i
    fin_cases i <;> simp [W,pattern,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem kernel_span (z : Fin 4 → ℂ) : W.mulVec z=0 ↔ ∃ a : ℂ,z=a • ![1,-1,-1,1] := by
  rw [kernel_iff]
  constructor
  · intro h
    refine ⟨z 0,?_⟩
    rw [h]
    ext i
    fin_cases i <;> simp [pattern]
  · rintro ⟨a,rfl⟩
    ext i
    fin_cases i <;> simp [pattern]

noncomputable def parameters : ℂ ≃ₗ[ℂ] LinearMap.ker W.mulVecLin where
  toFun a := ⟨pattern a,(kernel_iff _).2 rfl⟩
  invFun z := z.1 0
  left_inv a := rfl
  right_inv z := by
    apply Subtype.ext
    exact ((kernel_iff z.1).1 z.2).symm
  map_add' a b := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [pattern,add_comm]
  map_smul' a b := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [pattern]

theorem kernel_dimension : Module.finrank ℂ (LinearMap.ker W.mulVecLin)=1 := by
  simpa using (LinearEquiv.finrank_eq parameters).symm

theorem rank_three : W.rank=3 := by
  have h := LinearMap.finrank_range_add_finrank_ker W.mulVecLin
  rw [kernel_dimension] at h
  change W.rank+1=Module.finrank ℂ (Fin 4 → ℂ) at h
  norm_num at h
  omega

theorem relations (z : Fin 4 → ℂ) (h : W.mulVec z=0) :
    z 0=z 3 ∧ z 1=z 2 ∧ z 1= -z 0 := by
  have hz := (kernel_iff z).1 h
  rw [hz]
  exact ⟨rfl,rfl,rfl⟩

end MainTheory.OrderSevenWalshMatrix
