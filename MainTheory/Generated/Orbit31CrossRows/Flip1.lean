import MainTheory.Orbit31SupportBase

/-! Actual orbit-31 cross-Pauli rows for physical flip (0,).
The support incidences, signs and complete row-space normal form are checked.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 1000000
namespace MainTheory.Generated.Orbit31CrossRows.Flip1
open MainTheory.Orbit31SupportBase
open MainTheory.OrderEightSupportDisplays (bits)
open SixQubit.Orbit31
open scoped BigOperators
noncomputable section

def top (j : Fin 16) : SS.BitString 6 := fun k => !(bottom j k)
def src : Fin 8 → Fin 16 := ![⟨0,by decide⟩,⟨4,by decide⟩,⟨1,by decide⟩,⟨5,by decide⟩,⟨2,by decide⟩,⟨6,by decide⟩,⟨3,by decide⟩,⟨7,by decide⟩]
def dst : Fin 8 → Fin 16 := ![⟨4,by decide⟩,⟨0,by decide⟩,⟨5,by decide⟩,⟨1,by decide⟩,⟨6,by decide⟩,⟨2,by decide⟩,⟨7,by decide⟩,⟨3,by decide⟩]
def flip : SS.BitString 6 := bits 32
def dressing : Fin 12 → SS.BitString 6 := fun r => bits (![0,1,2,4,8,16,32,33,34,36,40,48] r)
def rows : Matrix (Fin 12) (Fin 8) ℤ := ![![1,1,1,1,1,1,1,1],![1,-1,-1,1,-1,1,1,-1],![1,-1,-1,1,1,-1,-1,1],![1,-1,1,-1,-1,1,-1,1],![1,-1,1,-1,1,-1,1,-1],![1,-1,1,-1,1,-1,1,-1],![-1,-1,-1,-1,-1,-1,-1,-1],![-1,1,1,-1,1,-1,-1,1],![-1,1,1,-1,-1,1,1,-1],![-1,1,-1,1,1,-1,1,-1],![-1,1,-1,1,-1,1,-1,1],![-1,1,-1,1,-1,1,-1,1]]
def W : Matrix (Fin 12) (Fin 8) ℂ := fun i j => rows i j
def products (c d : SS.State 6 ℂ) : Fin 8 → ℂ := fun j =>
  star (c (bottom (src j))) * d (top (dst j))

theorem incidences : S1.filter (fun y => SS.bxor y flip ∈ S0) =
    ({top ⟨4,by decide⟩,top ⟨0,by decide⟩,top ⟨5,by decide⟩,top ⟨1,by decide⟩,top ⟨6,by decide⟩,top ⟨2,by decide⟩,top ⟨7,by decide⟩,top ⟨3,by decide⟩} : Finset (SS.BitString 6)) := by decide +kernel

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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨0,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨5,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨1,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨6,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨2,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨0,by decide⟩) (top ⟨3,by decide⟩) = false by decide +kernel]
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨0,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨5,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨1,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨6,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨2,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨1,by decide⟩) (top ⟨3,by decide⟩) = true by decide +kernel]
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨0,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨5,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨1,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨6,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨2,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨7,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨2,by decide⟩) (top ⟨3,by decide⟩) = false by decide +kernel]
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨0,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨5,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨1,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨6,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨2,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨7,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨3,by decide⟩) (top ⟨3,by decide⟩) = false by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row4 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨4,by decide⟩) = W.mulVec (products c d) ⟨4,by decide⟩ := by
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨4,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨4,by decide⟩) (top ⟨0,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨4,by decide⟩) (top ⟨5,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨4,by decide⟩) (top ⟨1,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨4,by decide⟩) (top ⟨6,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨4,by decide⟩) (top ⟨2,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨4,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨4,by decide⟩) (top ⟨3,by decide⟩) = true by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row5 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨5,by decide⟩) = W.mulVec (products c d) ⟨5,by decide⟩ := by
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨5,by decide⟩) (top ⟨4,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨5,by decide⟩) (top ⟨0,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨5,by decide⟩) (top ⟨5,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨5,by decide⟩) (top ⟨1,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨5,by decide⟩) (top ⟨6,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨5,by decide⟩) (top ⟨2,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨5,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨5,by decide⟩) (top ⟨3,by decide⟩) = true by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row6 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨6,by decide⟩) = W.mulVec (products c d) ⟨6,by decide⟩ := by
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨6,by decide⟩) (top ⟨4,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨6,by decide⟩) (top ⟨0,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨6,by decide⟩) (top ⟨5,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨6,by decide⟩) (top ⟨1,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨6,by decide⟩) (top ⟨6,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨6,by decide⟩) (top ⟨2,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨6,by decide⟩) (top ⟨7,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨6,by decide⟩) (top ⟨3,by decide⟩) = true by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row7 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨7,by decide⟩) = W.mulVec (products c d) ⟨7,by decide⟩ := by
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨7,by decide⟩) (top ⟨4,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨7,by decide⟩) (top ⟨0,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨7,by decide⟩) (top ⟨5,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨7,by decide⟩) (top ⟨1,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨7,by decide⟩) (top ⟨6,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨7,by decide⟩) (top ⟨2,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨7,by decide⟩) (top ⟨7,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨7,by decide⟩) (top ⟨3,by decide⟩) = false by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row8 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨8,by decide⟩) = W.mulVec (products c d) ⟨8,by decide⟩ := by
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨8,by decide⟩) (top ⟨4,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨8,by decide⟩) (top ⟨0,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨8,by decide⟩) (top ⟨5,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨8,by decide⟩) (top ⟨1,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨8,by decide⟩) (top ⟨6,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨8,by decide⟩) (top ⟨2,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨8,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨8,by decide⟩) (top ⟨3,by decide⟩) = true by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row9 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨9,by decide⟩) = W.mulVec (products c d) ⟨9,by decide⟩ := by
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨9,by decide⟩) (top ⟨4,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨9,by decide⟩) (top ⟨0,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨9,by decide⟩) (top ⟨5,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨9,by decide⟩) (top ⟨1,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨9,by decide⟩) (top ⟨6,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨9,by decide⟩) (top ⟨2,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨9,by decide⟩) (top ⟨7,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨9,by decide⟩) (top ⟨3,by decide⟩) = true by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row10 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨10,by decide⟩) = W.mulVec (products c d) ⟨10,by decide⟩ := by
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨10,by decide⟩) (top ⟨4,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨10,by decide⟩) (top ⟨0,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨10,by decide⟩) (top ⟨5,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨10,by decide⟩) (top ⟨1,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨10,by decide⟩) (top ⟨6,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨10,by decide⟩) (top ⟨2,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨10,by decide⟩) (top ⟨7,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨10,by decide⟩) (top ⟨3,by decide⟩) = false by decide +kernel]
  conv_rhs => norm_num [W,rows,products,src,dst,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ]
  conv_lhs => norm_num [SixQubit.signMul]

theorem row11 (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d flip (dressing ⟨11,by decide⟩) = W.mulVec (products c d) ⟨11,by decide⟩ := by
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
  rw [show SS.bxor (top ⟨4,by decide⟩) flip = bottom ⟨0,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨11,by decide⟩) (top ⟨4,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨0,by decide⟩) flip = bottom ⟨4,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨11,by decide⟩) (top ⟨0,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨5,by decide⟩) flip = bottom ⟨1,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨11,by decide⟩) (top ⟨5,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨1,by decide⟩) flip = bottom ⟨5,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨11,by decide⟩) (top ⟨1,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨6,by decide⟩) flip = bottom ⟨2,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨11,by decide⟩) (top ⟨6,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨2,by decide⟩) flip = bottom ⟨6,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨11,by decide⟩) (top ⟨2,by decide⟩) = false by decide +kernel]
  rw [show SS.bxor (top ⟨7,by decide⟩) flip = bottom ⟨3,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨11,by decide⟩) (top ⟨7,by decide⟩) = true by decide +kernel]
  rw [show SS.bxor (top ⟨3,by decide⟩) flip = bottom ⟨7,by decide⟩ by decide +kernel]
  rw [show SS.bdot (dressing ⟨11,by decide⟩) (top ⟨3,by decide⟩) = false by decide +kernel]
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
  · simpa only [Pi.zero_apply] using (row4 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨4,by decide⟩) (dressing_weight ⟨4,by decide⟩))
  · simpa only [Pi.zero_apply] using (row5 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨5,by decide⟩) (dressing_weight ⟨5,by decide⟩))
  · simpa only [Pi.zero_apply] using (row6 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨6,by decide⟩) (dressing_weight ⟨6,by decide⟩))
  · simpa only [Pi.zero_apply] using (row7 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨7,by decide⟩) (dressing_weight ⟨7,by decide⟩))
  · simpa only [Pi.zero_apply] using (row8 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨8,by decide⟩) (dressing_weight ⟨8,by decide⟩))
  · simpa only [Pi.zero_apply] using (row9 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨9,by decide⟩) (dressing_weight ⟨9,by decide⟩))
  · simpa only [Pi.zero_apply] using (row10 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨10,by decide⟩) (dressing_weight ⟨10,by decide⟩))
  · simpa only [Pi.zero_apply] using (row11 c d).symm.trans
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
        flip (dressing ⟨11,by decide⟩) (dressing_weight ⟨11,by decide⟩))

def freeIndices : Fin 3 → Fin 8 := ![⟨3,by decide⟩,⟨5,by decide⟩,⟨7,by decide⟩]
def pattern (p : Fin 3 → ℂ) : Fin 8 → ℂ := ![-1 * p ⟨0,by decide⟩ + -1 * p ⟨1,by decide⟩ + -1 * p ⟨2,by decide⟩,-1 * p ⟨0,by decide⟩ + -1 * p ⟨1,by decide⟩ + -1 * p ⟨2,by decide⟩,1 * p ⟨0,by decide⟩,p ⟨0,by decide⟩,1 * p ⟨1,by decide⟩,p ⟨1,by decide⟩,1 * p ⟨2,by decide⟩,p ⟨2,by decide⟩]

theorem kernel_iff (t : Fin 8 → ℂ) :
    W.mulVec t = 0 ↔ t = pattern (fun j => t (freeIndices j)) := by
  constructor
  · intro h
    have h0 := congrFun h ⟨0,by decide⟩
    have h1 := congrFun h ⟨1,by decide⟩
    have h2 := congrFun h ⟨2,by decide⟩
    have h3 := congrFun h ⟨3,by decide⟩
    have h4 := congrFun h ⟨4,by decide⟩
    have h5 := congrFun h ⟨5,by decide⟩
    have h6 := congrFun h ⟨6,by decide⟩
    have h7 := congrFun h ⟨7,by decide⟩
    have h8 := congrFun h ⟨8,by decide⟩
    have h9 := congrFun h ⟨9,by decide⟩
    have h10 := congrFun h ⟨10,by decide⟩
    have h11 := congrFun h ⟨11,by decide⟩
    norm_num [W,rows,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    have e0 : t ⟨0,by decide⟩ = -1 * t ⟨3,by decide⟩ + -1 * t ⟨5,by decide⟩ + -1 * t ⟨7,by decide⟩ := by
      norm_num
      linear_combination (1/2) * h0 + (1/4) * h1 + (1/4) * h2 + (1/4) * h3 + (-1/4) * h4
    have e1 : t ⟨1,by decide⟩ = -1 * t ⟨3,by decide⟩ + -1 * t ⟨5,by decide⟩ + -1 * t ⟨7,by decide⟩ := by
      norm_num
      linear_combination (1/2) * h0 + (-1/2) * h4
    have e2 : t ⟨2,by decide⟩ = 1 * t ⟨3,by decide⟩ := by
      norm_num
      linear_combination (-1/4) * h1 + (-1/4) * h2 + (1/4) * h3 + (1/4) * h4
    have e4 : t ⟨4,by decide⟩ = 1 * t ⟨5,by decide⟩ := by
      norm_num
      linear_combination (-1/4) * h1 + (1/4) * h2 + (-1/4) * h3 + (1/4) * h4
    have e6 : t ⟨6,by decide⟩ = 1 * t ⟨7,by decide⟩ := by
      norm_num
      linear_combination (1/4) * h1 + (-1/4) * h2 + (-1/4) * h3 + (1/4) * h4
    funext j
    fin_cases j
    · exact e0
    · exact e1
    · exact e2
    · rfl
    · exact e4
    · rfl
    · exact e6
    · rfl
  · intro h
    rw [h]
    ext r
    fin_cases r <;> norm_num [W,rows,pattern,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,Fin.succ] <;> ring

def parameters : (Fin 3 → ℂ) ≃ₗ[ℂ] LinearMap.ker W.mulVecLin where
  toFun p := ⟨pattern p,(kernel_iff _).mpr (by funext j; fin_cases j <;> rfl)⟩
  invFun t := fun j => t.1 (freeIndices j)
  left_inv p := by funext j; fin_cases j <;> rfl
  right_inv t := by apply Subtype.ext; exact ((kernel_iff _).mp t.2).symm
  map_add' p q := by apply Subtype.ext; funext j; fin_cases j <;> norm_num [pattern] <;> ring
  map_smul' a p := by apply Subtype.ext; funext j; fin_cases j <;> norm_num [pattern] <;> ring

theorem kernel_dimension : Module.finrank ℂ (LinearMap.ker W.mulVecLin) = 3 := by
  simpa using (LinearEquiv.finrank_eq parameters).symm

theorem rank : W.rank = 5 := by
  have h := LinearMap.finrank_range_add_finrank_ker W.mulVecLin
  rw [kernel_dimension] at h
  change W.rank + 3 = Module.finrank ℂ (Fin 8 → ℂ) at h
  norm_num at h
  omega

end
end MainTheory.Generated.Orbit31CrossRows.Flip1
