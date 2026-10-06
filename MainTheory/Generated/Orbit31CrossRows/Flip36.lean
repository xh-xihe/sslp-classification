import MainTheory.Orbit31SupportBase

/-! Actual orbit-31 cross-Pauli rows for physical flip (2, 5).
The support incidences, signs and complete row-space normal form are checked.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31CrossRows.Flip36
open MainTheory.Orbit31SupportBase
open MainTheory.OrderEightSupportDisplays (bits)
open SixQubit.Orbit31
open scoped BigOperators
noncomputable section

def top (j : Fin 16) : SS.BitString 6 := fun k => !(bottom j k)
def src : Fin 8 → Fin 16 := ![⟨4,by decide⟩,⟨11,by decide⟩,⟨5,by decide⟩,⟨10,by decide⟩,⟨6,by decide⟩,⟨9,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩]
def dst : Fin 8 → Fin 16 := ![⟨11,by decide⟩,⟨4,by decide⟩,⟨10,by decide⟩,⟨5,by decide⟩,⟨9,by decide⟩,⟨6,by decide⟩,⟨8,by decide⟩,⟨7,by decide⟩]
def flip : SS.BitString 6 := bits 9
def dressing : Fin 4 → SS.BitString 6 := fun r => bits (![0,1,8,9] r)
def rows : Matrix (Fin 4) (Fin 8) ℤ := ![![1,1,1,1,1,1,1,1],![1,1,-1,-1,-1,-1,1,1],![1,1,1,1,1,1,1,1],![1,1,-1,-1,-1,-1,1,1]]
def W : Matrix (Fin 4) (Fin 8) ℂ := fun i j => rows i j
def products (c d : SS.State 6 ℂ) : Fin 8 → ℂ := fun j =>
  star (c (bottom (src j))) * d (top (dst j))

theorem incidences : S1.filter (fun y => SS.bxor y flip ∈ S0) =
    ({top ⟨11,by decide⟩,top ⟨4,by decide⟩,top ⟨10,by decide⟩,top ⟨5,by decide⟩,top ⟨9,by decide⟩,top ⟨6,by decide⟩,top ⟨8,by decide⟩,top ⟨7,by decide⟩} : Finset (SS.BitString 6)) := by decide +kernel

theorem source_incidence : ∀ j, SS.bxor (top (dst j)) flip = bottom (src j) := by decide +kernel
theorem dressing_weight : ∀ r, (⟨flip,dressing r⟩ : SS.PauliString 6).wt ≤ 2 := by decide +kernel
theorem actual_signs : ∀ r j,
    (if SS.bdot (dressing r) (top (dst j)) then (-1 : ℤ) else 1) = rows r j := by decide +kernel

theorem row0 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨0,by decide⟩) = W.mulVec (products c d) ⟨0,by decide⟩ := by
  unfold SixQubit.offSumOn
  rw [incidences,
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  rw [show SS.bxor (top ⟨11,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨11,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨11,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨10,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨10,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨10,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨5,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨9,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨9,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨9,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨6,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨8,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨8,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨8,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row1 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨1,by decide⟩) = W.mulVec (products c d) ⟨1,by decide⟩ := by
  unfold SixQubit.offSumOn
  rw [incidences,
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  rw [show SS.bxor (top ⟨11,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨11,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨11,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨10,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨10,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨10,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨5,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨9,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨9,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨9,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨6,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨8,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨8,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨8,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row2 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨2,by decide⟩) = W.mulVec (products c d) ⟨2,by decide⟩ := by
  unfold SixQubit.offSumOn
  rw [incidences,
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  rw [show SS.bxor (top ⟨11,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨11,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨11,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨10,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨10,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨10,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨5,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨9,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨9,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨9,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨6,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨8,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨8,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨8,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row3 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨3,by decide⟩) = W.mulVec (products c d) ⟨3,by decide⟩ := by
  unfold SixQubit.offSumOn
  rw [incidences,
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_insert (by decide +kernel),
    Finset.sum_singleton]
  rw [show SS.bxor (top ⟨11,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨11,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨11,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨10,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨10,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨10,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨5,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨9,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨9,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨9,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨6,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨8,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨8,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨8,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem physical (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hkl : SS.HasDistance ![c,d] 3) : W.mulVec (products c d) = 0 := by
  ext r
  fin_cases r
  · simpa only [Pi.zero_apply] using (row0 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨0,by decide⟩) (dressing_weight ⟨0,by decide⟩))
  · simpa only [Pi.zero_apply] using (row1 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨1,by decide⟩) (dressing_weight ⟨1,by decide⟩))
  · simpa only [Pi.zero_apply] using (row2 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨2,by decide⟩) (dressing_weight ⟨2,by decide⟩))
  · simpa only [Pi.zero_apply] using (row3 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨3,by decide⟩) (dressing_weight ⟨3,by decide⟩))

def freeIndices : Fin 6 → Fin 8 := ![⟨1,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩]
def pattern (p : Fin 6 → ℂ) : Fin 8 → ℂ := ![-1 * p ⟨0,by decide⟩ + -1 * p ⟨4,by decide⟩ + -1 * p ⟨5,by decide⟩,p ⟨0,by decide⟩,-1 * p ⟨1,by decide⟩ + -1 * p ⟨2,by decide⟩ + -1 * p ⟨3,by decide⟩,p ⟨1,by decide⟩,p ⟨2,by decide⟩,p ⟨3,by decide⟩,p ⟨4,by decide⟩,p ⟨5,by decide⟩]

theorem kernel_iff (t : Fin 8 → ℂ) :
    W.mulVec t = 0 ↔ t = pattern (fun j => t (freeIndices j)) := by
  constructor
  · intro h
    have h0 := congrFun h ⟨0,by decide⟩
    have h1 := congrFun h ⟨1,by decide⟩
    have h2 := congrFun h ⟨2,by decide⟩
    have h3 := congrFun h ⟨3,by decide⟩
    norm_num [W,rows,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2 h3
    have e0 : t ⟨0,by decide⟩ = -1 * t ⟨1,by decide⟩ + -1 * t ⟨6,by decide⟩ + -1 * t ⟨7,by decide⟩ := by
      norm_num
      linear_combination (1/2) * h0 + (1/2) * h1
    have e2 : t ⟨2,by decide⟩ = -1 * t ⟨3,by decide⟩ + -1 * t ⟨4,by decide⟩ + -1 * t ⟨5,by decide⟩ := by
      norm_num
      linear_combination (1/2) * h0 + (-1/2) * h1
    funext j
    fin_cases j
    · exact e0
    · rfl
    · exact e2
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · intro h
    rw [h]
    ext r
    fin_cases r <;> norm_num [W,rows,pattern,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Fin.succ] <;> ring

def parameters : (Fin 6 → ℂ) ≃ₗ[ℂ] LinearMap.ker W.mulVecLin where
  toFun p := ⟨pattern p,(kernel_iff _).mpr (by funext j; fin_cases j <;> rfl)⟩
  invFun t := fun j => t.1 (freeIndices j)
  left_inv p := by funext j; fin_cases j <;> rfl
  right_inv t := by apply Subtype.ext; exact ((kernel_iff _).mp t.2).symm
  map_add' p q := by apply Subtype.ext; funext j; fin_cases j <;> norm_num [pattern] <;> ring
  map_smul' a p := by apply Subtype.ext; funext j; fin_cases j <;> norm_num [pattern] <;> ring

theorem kernel_dimension : Module.finrank ℂ (LinearMap.ker W.mulVecLin) = 6 := by
  simpa using (LinearEquiv.finrank_eq parameters).symm

theorem rank : W.rank = 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker W.mulVecLin
  rw [kernel_dimension] at h
  change W.rank + 6 = Module.finrank ℂ (Fin 8 → ℂ) at h
  norm_num at h
  omega

end
end MainTheory.Generated.Orbit31CrossRows.Flip36
