import SixQubit.CodeOrbit33
import MainTheory.Orbit33PrintedReflection

/-! Every printed block norm and matrix reflection in actual physical coordinates.
The rational row combinations are checked by Lean, independently of no-code.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit33PrintedBlocks
open SixQubit.Orbit33
open scoped BigOperators
noncomputable section

def VectorMoments (q r : Fin 12 → ℝ) : Prop := MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩)

theorem norm_bottom_0 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (q ⟨0,by decide⟩) + (q ⟨6,by decide⟩) - 3/10=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination 1 * hm.n0 + (-7/10) * hm.n1 + (-7/10) * hm.m2 + (-7/10) * hm.m3 + (-7/20) * hm.m4 + (-7/20) * hm.m5 + (-7/20) * hm.m6 + (1/4) * hm.c23 + (-1/4) * hm.c24 + (1/2) * hm.c25 + (1/2) * hm.c26 + (3/4) * hm.c34

theorem norm_bottom_1 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (q ⟨1,by decide⟩) + (q ⟨7,by decide⟩) - 1/5=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/5) * hm.n1 + (1/5) * hm.m2 + (1/5) * hm.m3 + (1/10) * hm.m4 + (1/10) * hm.m5 + (1/10) * hm.m6 + (-1/2) * hm.c23 + (-1/2) * hm.c24 + (1/2) * hm.c34

theorem norm_bottom_2 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (q ⟨2,by decide⟩) + (q ⟨8,by decide⟩) - 1/5=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/5) * hm.n1 + (1/5) * hm.m2 + (1/5) * hm.m3 + (1/10) * hm.m4 + (1/10) * hm.m5 + (1/10) * hm.m6 + (-1/2) * hm.c23 + (1/2) * hm.c24 + (-1/2) * hm.c34

theorem norm_bottom_3 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (q ⟨3,by decide⟩) + (q ⟨9,by decide⟩) - 1/10=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/10) * hm.n1 + (1/10) * hm.m2 + (1/10) * hm.m3 + (1/20) * hm.m4 + (1/20) * hm.m5 + (1/20) * hm.m6 + (1/4) * hm.c23 + (-1/4) * hm.c24 + (-1/2) * hm.c25 + (1/2) * hm.c26 + (-1/4) * hm.c34

theorem norm_bottom_4 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (q ⟨10,by decide⟩) + (q ⟨4,by decide⟩) - 1/10=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/10) * hm.n1 + (1/10) * hm.m2 + (1/10) * hm.m3 + (1/20) * hm.m4 + (1/20) * hm.m5 + (1/20) * hm.m6 + (1/4) * hm.c23 + (-1/4) * hm.c24 + (1/2) * hm.c25 + (-1/2) * hm.c26 + (-1/4) * hm.c34

theorem norm_bottom_5 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (q ⟨11,by decide⟩) + (q ⟨5,by decide⟩) - 1/10=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/10) * hm.n1 + (1/10) * hm.m2 + (1/10) * hm.m3 + (1/20) * hm.m4 + (1/20) * hm.m5 + (1/20) * hm.m6 + (1/4) * hm.c23 + (3/4) * hm.c24 + (-1/2) * hm.c25 + (-1/2) * hm.c26 + (-1/4) * hm.c34

theorem norm_top_0 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (r ⟨11,by decide⟩) + (r ⟨5,by decide⟩) - 3/10=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (3/10) * hm.n1 + (3/10) * hm.m2 + (3/10) * hm.m3 + (3/20) * hm.m4 + (3/20) * hm.m5 + (3/20) * hm.m6 + (-1/4) * hm.c23 + (1/4) * hm.c24 + (-1/2) * hm.c25 + (-1/2) * hm.c26 + (-3/4) * hm.c34

theorem norm_top_1 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (r ⟨10,by decide⟩) + (r ⟨4,by decide⟩) - 1/5=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/5) * hm.n1 + (-4/5) * hm.m2 + (1/5) * hm.m3 + (1/10) * hm.m4 + (1/10) * hm.m5 + (1/10) * hm.m6 + (1/2) * hm.c23 + (1/2) * hm.c24 + (-1/2) * hm.c34

theorem norm_top_2 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (r ⟨3,by decide⟩) + (r ⟨9,by decide⟩) - 1/5=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/5) * hm.n1 + (1/5) * hm.m2 + (-4/5) * hm.m3 + (1/10) * hm.m4 + (1/10) * hm.m5 + (1/10) * hm.m6 + (1/2) * hm.c23 + (-1/2) * hm.c24 + (1/2) * hm.c34

theorem norm_top_3 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (r ⟨2,by decide⟩) + (r ⟨8,by decide⟩) - 1/10=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/10) * hm.n1 + (1/10) * hm.m2 + (1/10) * hm.m3 + (-9/20) * hm.m4 + (-9/20) * hm.m5 + (11/20) * hm.m6 + (-1/4) * hm.c23 + (1/4) * hm.c24 + (1/2) * hm.c25 + (-1/2) * hm.c26 + (1/4) * hm.c34

theorem norm_top_4 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (r ⟨1,by decide⟩) + (r ⟨7,by decide⟩) - 1/10=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/10) * hm.n1 + (1/10) * hm.m2 + (1/10) * hm.m3 + (-9/20) * hm.m4 + (11/20) * hm.m5 + (-9/20) * hm.m6 + (-1/4) * hm.c23 + (1/4) * hm.c24 + (-1/2) * hm.c25 + (1/2) * hm.c26 + (1/4) * hm.c34

theorem norm_top_5 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : (r ⟨0,by decide⟩) + (r ⟨6,by decide⟩) - 1/10=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (1/10) * hm.n1 + (1/10) * hm.m2 + (1/10) * hm.m3 + (11/20) * hm.m4 + (-9/20) * hm.m5 + (-9/20) * hm.m6 + (-1/4) * hm.c23 + (-3/4) * hm.c24 + (1/2) * hm.c25 + (1/2) * hm.c26 + (1/4) * hm.c34

theorem diagonal_0_0 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : 2*(q ⟨0,by decide⟩)/5 - 3*(q ⟨1,by decide⟩)/5 - 3*(q ⟨2,by decide⟩)/5 - 3*(q ⟨3,by decide⟩)/5 - 3*(q ⟨4,by decide⟩)/5 - 3*(q ⟨5,by decide⟩)/5 + (r ⟨5,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (2/5) * hm.n0 + (-2/5) * hm.n1 + (-2/5) * hm.m1 + (-2/5) * hm.m2 + (-2/5) * hm.m3 + (-1/5) * hm.m4 + (-1/5) * hm.m5 + (-1/5) * hm.m6 + (2/5) * hm.c12 + (2/5) * hm.c13 + (1/5) * hm.c14 + (1/5) * hm.c15 + (1/5) * hm.c16

theorem diagonal_0_1 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -2*(q ⟨0,by decide⟩)/5 + 3*(q ⟨1,by decide⟩)/5 - 2*(q ⟨2,by decide⟩)/5 - 2*(q ⟨3,by decide⟩)/5 - 2*(q ⟨4,by decide⟩)/5 - 2*(q ⟨5,by decide⟩)/5 + (r ⟨4,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-2/5) * hm.n0 + (2/5) * hm.n1 + (2/5) * hm.m1 + (-3/5) * hm.m2 + (2/5) * hm.m3 + (1/5) * hm.m4 + (1/5) * hm.m5 + (1/5) * hm.m6 + (3/5) * hm.c12 + (-2/5) * hm.c13 + (-1/5) * hm.c14 + (-1/5) * hm.c15 + (-1/5) * hm.c16

theorem diagonal_0_2 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -2*(q ⟨0,by decide⟩)/5 - 2*(q ⟨1,by decide⟩)/5 + 3*(q ⟨2,by decide⟩)/5 - 2*(q ⟨3,by decide⟩)/5 - 2*(q ⟨4,by decide⟩)/5 - 2*(q ⟨5,by decide⟩)/5 + (r ⟨3,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-2/5) * hm.n0 + (2/5) * hm.n1 + (2/5) * hm.m1 + (2/5) * hm.m2 + (-3/5) * hm.m3 + (1/5) * hm.m4 + (1/5) * hm.m5 + (1/5) * hm.m6 + (-2/5) * hm.c12 + (3/5) * hm.c13 + (-1/5) * hm.c14 + (-1/5) * hm.c15 + (-1/5) * hm.c16

theorem diagonal_0_3 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -(q ⟨0,by decide⟩)/5 - (q ⟨1,by decide⟩)/5 - (q ⟨2,by decide⟩)/5 + 4*(q ⟨3,by decide⟩)/5 - (q ⟨4,by decide⟩)/5 - (q ⟨5,by decide⟩)/5 + (r ⟨2,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-1/5) * hm.n0 + (1/5) * hm.n1 + (1/5) * hm.m1 + (1/5) * hm.m2 + (1/5) * hm.m3 + (-2/5) * hm.m4 + (-2/5) * hm.m5 + (3/5) * hm.m6 + (-1/5) * hm.c12 + (-1/5) * hm.c13 + (2/5) * hm.c14 + (2/5) * hm.c15 + (-3/5) * hm.c16

theorem diagonal_0_4 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -(q ⟨0,by decide⟩)/5 - (q ⟨1,by decide⟩)/5 - (q ⟨2,by decide⟩)/5 - (q ⟨3,by decide⟩)/5 + 4*(q ⟨4,by decide⟩)/5 - (q ⟨5,by decide⟩)/5 + (r ⟨1,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-1/5) * hm.n0 + (1/5) * hm.n1 + (1/5) * hm.m1 + (1/5) * hm.m2 + (1/5) * hm.m3 + (-2/5) * hm.m4 + (3/5) * hm.m5 + (-2/5) * hm.m6 + (-1/5) * hm.c12 + (-1/5) * hm.c13 + (2/5) * hm.c14 + (-3/5) * hm.c15 + (2/5) * hm.c16

theorem diagonal_0_5 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -(q ⟨0,by decide⟩)/5 - (q ⟨1,by decide⟩)/5 - (q ⟨2,by decide⟩)/5 - (q ⟨3,by decide⟩)/5 - (q ⟨4,by decide⟩)/5 + 4*(q ⟨5,by decide⟩)/5 + (r ⟨0,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-1/5) * hm.n0 + (1/5) * hm.n1 + (1/5) * hm.m1 + (1/5) * hm.m2 + (1/5) * hm.m3 + (3/5) * hm.m4 + (-2/5) * hm.m5 + (-2/5) * hm.m6 + (-1/5) * hm.c12 + (-1/5) * hm.c13 + (-3/5) * hm.c14 + (2/5) * hm.c15 + (2/5) * hm.c16

theorem diagonal_1_0 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -3*(q ⟨10,by decide⟩)/5 - 3*(q ⟨11,by decide⟩)/5 + 2*(q ⟨6,by decide⟩)/5 - 3*(q ⟨7,by decide⟩)/5 - 3*(q ⟨8,by decide⟩)/5 - 3*(q ⟨9,by decide⟩)/5 + (r ⟨11,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (2/5) * hm.m1 + (-2/5) * hm.c12 + (-2/5) * hm.c13 + (-1/5) * hm.c14 + (-1/5) * hm.c15 + (-1/5) * hm.c16

theorem diagonal_1_1 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -2*(q ⟨10,by decide⟩)/5 - 2*(q ⟨11,by decide⟩)/5 - 2*(q ⟨6,by decide⟩)/5 + 3*(q ⟨7,by decide⟩)/5 - 2*(q ⟨8,by decide⟩)/5 - 2*(q ⟨9,by decide⟩)/5 + (r ⟨10,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-2/5) * hm.m1 + (-3/5) * hm.c12 + (2/5) * hm.c13 + (1/5) * hm.c14 + (1/5) * hm.c15 + (1/5) * hm.c16

theorem diagonal_1_2 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -2*(q ⟨10,by decide⟩)/5 - 2*(q ⟨11,by decide⟩)/5 - 2*(q ⟨6,by decide⟩)/5 - 2*(q ⟨7,by decide⟩)/5 + 3*(q ⟨8,by decide⟩)/5 - 2*(q ⟨9,by decide⟩)/5 + (r ⟨9,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-2/5) * hm.m1 + (2/5) * hm.c12 + (-3/5) * hm.c13 + (1/5) * hm.c14 + (1/5) * hm.c15 + (1/5) * hm.c16

theorem diagonal_1_3 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -(q ⟨10,by decide⟩)/5 - (q ⟨11,by decide⟩)/5 - (q ⟨6,by decide⟩)/5 - (q ⟨7,by decide⟩)/5 - (q ⟨8,by decide⟩)/5 + 4*(q ⟨9,by decide⟩)/5 + (r ⟨8,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-1/5) * hm.m1 + (1/5) * hm.c12 + (1/5) * hm.c13 + (-2/5) * hm.c14 + (-2/5) * hm.c15 + (3/5) * hm.c16

theorem diagonal_1_4 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : 4*(q ⟨10,by decide⟩)/5 - (q ⟨11,by decide⟩)/5 - (q ⟨6,by decide⟩)/5 - (q ⟨7,by decide⟩)/5 - (q ⟨8,by decide⟩)/5 - (q ⟨9,by decide⟩)/5 + (r ⟨7,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-1/5) * hm.m1 + (1/5) * hm.c12 + (1/5) * hm.c13 + (-2/5) * hm.c14 + (3/5) * hm.c15 + (-2/5) * hm.c16

theorem diagonal_1_5 (q r : Fin 12 → ℝ) (hm : VectorMoments q r) : -(q ⟨10,by decide⟩)/5 + 4*(q ⟨11,by decide⟩)/5 - (q ⟨6,by decide⟩)/5 - (q ⟨7,by decide⟩)/5 - (q ⟨8,by decide⟩)/5 - (q ⟨9,by decide⟩)/5 + (r ⟨6,by decide⟩)=0 := by
  change MomentSystem (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩) (q ⟨11,by decide⟩) (r ⟨0,by decide⟩) (r ⟨1,by decide⟩) (r ⟨2,by decide⟩) (r ⟨3,by decide⟩) (r ⟨4,by decide⟩) (r ⟨5,by decide⟩) (r ⟨6,by decide⟩) (r ⟨7,by decide⟩) (r ⟨8,by decide⟩) (r ⟨9,by decide⟩) (r ⟨10,by decide⟩) (r ⟨11,by decide⟩) at hm
  linear_combination (-1/5) * hm.m1 + (1/5) * hm.c12 + (1/5) * hm.c13 + (3/5) * hm.c14 + (-2/5) * hm.c15 + (-2/5) * hm.c16

theorem off_diagonal_0 (c d : SS.State 6 ℂ)
    (Dg_w0 : diagBot c ef0 w0=diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6=diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5=diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11=diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4=diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10=diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3=diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9=diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2=diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8=diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1=diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7=diagTop d ef0 w7)
    : c y0 * star (c y6) + d z5 * star (d z11)
      = (3/5) * (c y0 * star (c y6) + c y1 * star (c y7) + c y2 * star (c y8) + c y3 * star (c y9) + c y4 * star (c y10) + c y5 * star (c y11)) := by
  rw [dbot_w0,dtop_w0] at Dg_w0
  rw [dbot_w6,dtop_w6] at Dg_w6
  rw [dbot_w5,dtop_w5] at Dg_w5
  rw [dbot_w11,dtop_w11] at Dg_w11
  rw [dbot_w4,dtop_w4] at Dg_w4
  rw [dbot_w10,dtop_w10] at Dg_w10
  rw [dbot_w3,dtop_w3] at Dg_w3
  rw [dbot_w9,dtop_w9] at Dg_w9
  rw [dbot_w2,dtop_w2] at Dg_w2
  rw [dbot_w8,dtop_w8] at Dg_w8
  rw [dbot_w1,dtop_w1] at Dg_w1
  rw [dbot_w7,dtop_w7] at Dg_w7
  linear_combination ((-3/20) : ℂ) * Dg_w0 + ((-3/20) : ℂ) * Dg_w6 + ((1/10) : ℂ) * Dg_w5 + ((1/10) : ℂ) * Dg_w11 + ((1/10) : ℂ) * Dg_w4 + ((1/10) : ℂ) * Dg_w10 + ((1/20) : ℂ) * Dg_w3 + ((1/20) : ℂ) * Dg_w9 + ((1/20) : ℂ) * Dg_w2 + ((1/20) : ℂ) * Dg_w8 + ((1/20) : ℂ) * Dg_w1 + ((1/20) : ℂ) * Dg_w7

theorem off_diagonal_1 (c d : SS.State 6 ℂ)
    (Dg_w0 : diagBot c ef0 w0=diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6=diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5=diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11=diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4=diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10=diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3=diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9=diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2=diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8=diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1=diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7=diagTop d ef0 w7)
    : c y1 * star (c y7) + d z4 * star (d z10)
      = (2/5) * (c y0 * star (c y6) + c y1 * star (c y7) + c y2 * star (c y8) + c y3 * star (c y9) + c y4 * star (c y10) + c y5 * star (c y11)) := by
  rw [dbot_w0,dtop_w0] at Dg_w0
  rw [dbot_w6,dtop_w6] at Dg_w6
  rw [dbot_w5,dtop_w5] at Dg_w5
  rw [dbot_w11,dtop_w11] at Dg_w11
  rw [dbot_w4,dtop_w4] at Dg_w4
  rw [dbot_w10,dtop_w10] at Dg_w10
  rw [dbot_w3,dtop_w3] at Dg_w3
  rw [dbot_w9,dtop_w9] at Dg_w9
  rw [dbot_w2,dtop_w2] at Dg_w2
  rw [dbot_w8,dtop_w8] at Dg_w8
  rw [dbot_w1,dtop_w1] at Dg_w1
  rw [dbot_w7,dtop_w7] at Dg_w7
  linear_combination ((-1/10) : ℂ) * Dg_w0 + ((-1/10) : ℂ) * Dg_w6 + ((3/20) : ℂ) * Dg_w5 + ((3/20) : ℂ) * Dg_w11 + ((-1/10) : ℂ) * Dg_w4 + ((-1/10) : ℂ) * Dg_w10 + ((-1/20) : ℂ) * Dg_w3 + ((-1/20) : ℂ) * Dg_w9 + ((-1/20) : ℂ) * Dg_w2 + ((-1/20) : ℂ) * Dg_w8 + ((-1/20) : ℂ) * Dg_w1 + ((-1/20) : ℂ) * Dg_w7

theorem off_diagonal_2 (c d : SS.State 6 ℂ)
    (Dg_w0 : diagBot c ef0 w0=diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6=diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5=diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11=diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4=diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10=diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3=diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9=diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2=diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8=diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1=diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7=diagTop d ef0 w7)
    : c y2 * star (c y8) + d z3 * star (d z9)
      = (2/5) * (c y0 * star (c y6) + c y1 * star (c y7) + c y2 * star (c y8) + c y3 * star (c y9) + c y4 * star (c y10) + c y5 * star (c y11)) := by
  rw [dbot_w0,dtop_w0] at Dg_w0
  rw [dbot_w6,dtop_w6] at Dg_w6
  rw [dbot_w5,dtop_w5] at Dg_w5
  rw [dbot_w11,dtop_w11] at Dg_w11
  rw [dbot_w4,dtop_w4] at Dg_w4
  rw [dbot_w10,dtop_w10] at Dg_w10
  rw [dbot_w3,dtop_w3] at Dg_w3
  rw [dbot_w9,dtop_w9] at Dg_w9
  rw [dbot_w2,dtop_w2] at Dg_w2
  rw [dbot_w8,dtop_w8] at Dg_w8
  rw [dbot_w1,dtop_w1] at Dg_w1
  rw [dbot_w7,dtop_w7] at Dg_w7
  linear_combination ((-1/10) : ℂ) * Dg_w0 + ((-1/10) : ℂ) * Dg_w6 + ((-1/10) : ℂ) * Dg_w5 + ((-1/10) : ℂ) * Dg_w11 + ((3/20) : ℂ) * Dg_w4 + ((3/20) : ℂ) * Dg_w10 + ((-1/20) : ℂ) * Dg_w3 + ((-1/20) : ℂ) * Dg_w9 + ((-1/20) : ℂ) * Dg_w2 + ((-1/20) : ℂ) * Dg_w8 + ((-1/20) : ℂ) * Dg_w1 + ((-1/20) : ℂ) * Dg_w7

theorem off_diagonal_3 (c d : SS.State 6 ℂ)
    (Dg_w0 : diagBot c ef0 w0=diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6=diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5=diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11=diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4=diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10=diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3=diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9=diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2=diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8=diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1=diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7=diagTop d ef0 w7)
    : c y3 * star (c y9) + d z2 * star (d z8)
      = (1/5) * (c y0 * star (c y6) + c y1 * star (c y7) + c y2 * star (c y8) + c y3 * star (c y9) + c y4 * star (c y10) + c y5 * star (c y11)) := by
  rw [dbot_w0,dtop_w0] at Dg_w0
  rw [dbot_w6,dtop_w6] at Dg_w6
  rw [dbot_w5,dtop_w5] at Dg_w5
  rw [dbot_w11,dtop_w11] at Dg_w11
  rw [dbot_w4,dtop_w4] at Dg_w4
  rw [dbot_w10,dtop_w10] at Dg_w10
  rw [dbot_w3,dtop_w3] at Dg_w3
  rw [dbot_w9,dtop_w9] at Dg_w9
  rw [dbot_w2,dtop_w2] at Dg_w2
  rw [dbot_w8,dtop_w8] at Dg_w8
  rw [dbot_w1,dtop_w1] at Dg_w1
  rw [dbot_w7,dtop_w7] at Dg_w7
  linear_combination ((-1/20) : ℂ) * Dg_w0 + ((-1/20) : ℂ) * Dg_w6 + ((-1/20) : ℂ) * Dg_w5 + ((-1/20) : ℂ) * Dg_w11 + ((-1/20) : ℂ) * Dg_w4 + ((-1/20) : ℂ) * Dg_w10 + ((1/10) : ℂ) * Dg_w3 + ((1/10) : ℂ) * Dg_w9 + ((1/10) : ℂ) * Dg_w2 + ((1/10) : ℂ) * Dg_w8 + ((-3/20) : ℂ) * Dg_w1 + ((-3/20) : ℂ) * Dg_w7

theorem off_diagonal_4 (c d : SS.State 6 ℂ)
    (Dg_w0 : diagBot c ef0 w0=diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6=diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5=diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11=diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4=diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10=diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3=diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9=diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2=diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8=diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1=diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7=diagTop d ef0 w7)
    : c y4 * star (c y10) + d z1 * star (d z7)
      = (1/5) * (c y0 * star (c y6) + c y1 * star (c y7) + c y2 * star (c y8) + c y3 * star (c y9) + c y4 * star (c y10) + c y5 * star (c y11)) := by
  rw [dbot_w0,dtop_w0] at Dg_w0
  rw [dbot_w6,dtop_w6] at Dg_w6
  rw [dbot_w5,dtop_w5] at Dg_w5
  rw [dbot_w11,dtop_w11] at Dg_w11
  rw [dbot_w4,dtop_w4] at Dg_w4
  rw [dbot_w10,dtop_w10] at Dg_w10
  rw [dbot_w3,dtop_w3] at Dg_w3
  rw [dbot_w9,dtop_w9] at Dg_w9
  rw [dbot_w2,dtop_w2] at Dg_w2
  rw [dbot_w8,dtop_w8] at Dg_w8
  rw [dbot_w1,dtop_w1] at Dg_w1
  rw [dbot_w7,dtop_w7] at Dg_w7
  linear_combination ((-1/20) : ℂ) * Dg_w0 + ((-1/20) : ℂ) * Dg_w6 + ((-1/20) : ℂ) * Dg_w5 + ((-1/20) : ℂ) * Dg_w11 + ((-1/20) : ℂ) * Dg_w4 + ((-1/20) : ℂ) * Dg_w10 + ((1/10) : ℂ) * Dg_w3 + ((1/10) : ℂ) * Dg_w9 + ((-3/20) : ℂ) * Dg_w2 + ((-3/20) : ℂ) * Dg_w8 + ((1/10) : ℂ) * Dg_w1 + ((1/10) : ℂ) * Dg_w7

theorem off_diagonal_5 (c d : SS.State 6 ℂ)
    (Dg_w0 : diagBot c ef0 w0=diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6=diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5=diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11=diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4=diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10=diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3=diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9=diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2=diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8=diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1=diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7=diagTop d ef0 w7)
    : c y5 * star (c y11) + d z0 * star (d z6)
      = (1/5) * (c y0 * star (c y6) + c y1 * star (c y7) + c y2 * star (c y8) + c y3 * star (c y9) + c y4 * star (c y10) + c y5 * star (c y11)) := by
  rw [dbot_w0,dtop_w0] at Dg_w0
  rw [dbot_w6,dtop_w6] at Dg_w6
  rw [dbot_w5,dtop_w5] at Dg_w5
  rw [dbot_w11,dtop_w11] at Dg_w11
  rw [dbot_w4,dtop_w4] at Dg_w4
  rw [dbot_w10,dtop_w10] at Dg_w10
  rw [dbot_w3,dtop_w3] at Dg_w3
  rw [dbot_w9,dtop_w9] at Dg_w9
  rw [dbot_w2,dtop_w2] at Dg_w2
  rw [dbot_w8,dtop_w8] at Dg_w8
  rw [dbot_w1,dtop_w1] at Dg_w1
  rw [dbot_w7,dtop_w7] at Dg_w7
  linear_combination ((-1/20) : ℂ) * Dg_w0 + ((-1/20) : ℂ) * Dg_w6 + ((-1/20) : ℂ) * Dg_w5 + ((-1/20) : ℂ) * Dg_w11 + ((-1/20) : ℂ) * Dg_w4 + ((-1/20) : ℂ) * Dg_w10 + ((-3/20) : ℂ) * Dg_w3 + ((-3/20) : ℂ) * Dg_w9 + ((1/10) : ℂ) * Dg_w2 + ((1/10) : ℂ) * Dg_w8 + ((1/10) : ℂ) * Dg_w1 + ((1/10) : ℂ) * Dg_w7


def bottom (i : Fin 6) (r : Fin 2) : SS.BitString 6 :=
  ![![y0,y1,y2,y3,y4,y5],![y6,y7,y8,y9,y10,y11]] r i
def top (i : Fin 6) (r : Fin 2) : SS.BitString 6 :=
  ![![z5,z4,z3,z2,z1,z0],![z11,z10,z9,z8,z7,z6]] r i
def CBlock (c : SS.State 6 ℂ) (i : Fin 6) : Fin 2 → ℂ := fun r => c (bottom i r)
def DBlock (d : SS.State 6 ℂ) (i : Fin 6) : Fin 2 → ℂ := fun r => d (top i r)
def outer (v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := fun r s => v r * star (v s)
def rho (c : SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ := ∑ i, outer (CBlock c i)
def R : Fin 6 → ℝ := ![3/10,1/5,1/5,1/10,1/10,1/10]
def nativeBottom : Fin 12 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11]
def nativeTop : Fin 12 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11]
def ActualMoments (c d : SS.State 6 ℂ) : Prop :=
  VectorMoments (fun j => Complex.normSq (c (nativeBottom j)))
    (fun j => Complex.normSq (d (nativeTop j)))

def tail : Fin 6 → SS.BitString 5 :=
  ![![false,false,false,false,false],![false,true,true,true,true],
    ![true,false,true,true,true],![true,true,false,false,true],
    ![true,true,false,true,false],![true,true,true,false,false]]
def embed (r : Fin 2) (t : SS.BitString 5) : SS.BitString 6 :=
  ![r=1,t 0,t 1,t 2,t 3,t 4]
theorem actual_words : ∀ i r,
    bottom i r=embed r (tail i) ∧ top i r=embed r (fun j => !(tail i j)) := by decide +kernel
theorem actual_fibers :
    Finset.univ.image (fun p : Fin 6 × Fin 2 => bottom p.1 p.2)=S0 ∧
    Finset.univ.image (fun p : Fin 6 × Fin 2 => top p.1 p.2)=S1 := by decide +kernel
def character (i j : Fin 6) : ℚ := if i=0 then 1 else
  if tail j ⟨i.val-1,by have := i.isLt; omega⟩ then -1 else 1
theorem actual_characters : MainTheory.Orbit33PrintedReflection.C=character := by decide +kernel

theorem block_norms (c d : SS.State 6 ℂ) (hm : ActualMoments c d) (i : Fin 6) :
    (∑ r : Fin 2, Complex.normSq (CBlock c i r))=R i ∧
    (∑ r : Fin 2, Complex.normSq (DBlock d i r))=R i := by
  fin_cases i
  · have hb := norm_bottom_0 _ _ hm
    have ht := norm_top_0 _ _ hm
    norm_num [nativeBottom,nativeTop] at hb ht
    norm_num [CBlock,DBlock,bottom,top,R,Fin.sum_univ_succ,Fin.succ]
    exact ⟨by linear_combination hb,by linear_combination ht⟩
  · have hb := norm_bottom_1 _ _ hm
    have ht := norm_top_1 _ _ hm
    norm_num [nativeBottom,nativeTop] at hb ht
    norm_num [CBlock,DBlock,bottom,top,R,Fin.sum_univ_succ,Fin.succ]
    exact ⟨by linear_combination hb,by linear_combination ht⟩
  · have hb := norm_bottom_2 _ _ hm
    have ht := norm_top_2 _ _ hm
    norm_num [nativeBottom,nativeTop] at hb ht
    norm_num [CBlock,DBlock,bottom,top,R,Fin.sum_univ_succ,Fin.succ]
    exact ⟨by linear_combination hb,by linear_combination ht⟩
  · have hb := norm_bottom_3 _ _ hm
    have ht := norm_top_3 _ _ hm
    norm_num [nativeBottom,nativeTop] at hb ht
    norm_num [CBlock,DBlock,bottom,top,R,Fin.sum_univ_succ,Fin.succ]
    exact ⟨by linear_combination hb,by linear_combination ht⟩
  · have hb := norm_bottom_4 _ _ hm
    have ht := norm_top_4 _ _ hm
    norm_num [nativeBottom,nativeTop] at hb ht
    norm_num [CBlock,DBlock,bottom,top,R,Fin.sum_univ_succ,Fin.succ]
    exact ⟨by linear_combination hb,by linear_combination ht⟩
  · have hb := norm_bottom_5 _ _ hm
    have ht := norm_top_5 _ _ hm
    norm_num [nativeBottom,nativeTop] at hb ht
    norm_num [CBlock,DBlock,bottom,top,R,Fin.sum_univ_succ,Fin.succ]
    exact ⟨by linear_combination hb,by linear_combination ht⟩

theorem matrix_reflection (c d : SS.State 6 ℂ) (hm : ActualMoments c d)
    (Dg_w0 : diagBot c ef0 w0=diagTop d ef0 w0)
    (Dg_w6 : diagBot c ef0 w6=diagTop d ef0 w6)
    (Dg_w5 : diagBot c ef0 w5=diagTop d ef0 w5)
    (Dg_w11 : diagBot c ef0 w11=diagTop d ef0 w11)
    (Dg_w4 : diagBot c ef0 w4=diagTop d ef0 w4)
    (Dg_w10 : diagBot c ef0 w10=diagTop d ef0 w10)
    (Dg_w3 : diagBot c ef0 w3=diagTop d ef0 w3)
    (Dg_w9 : diagBot c ef0 w9=diagTop d ef0 w9)
    (Dg_w2 : diagBot c ef0 w2=diagTop d ef0 w2)
    (Dg_w8 : diagBot c ef0 w8=diagTop d ef0 w8)
    (Dg_w1 : diagBot c ef0 w1=diagTop d ef0 w1)
    (Dg_w7 : diagBot c ef0 w7=diagTop d ef0 w7)
    (i : Fin 6) : outer (CBlock c i)+outer (DBlock d i)=(2*(R i : ℂ)) • rho c := by
  ext r s
  fin_cases i
  · fin_cases r <;> fin_cases s
    · have h := diagonal_0_0 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_0 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_0 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      have hc := congrArg star hc
      simp only [star_add,star_mul',star_star,star_div₀,star_ofNat] at hc
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have h := diagonal_1_0 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
  · fin_cases r <;> fin_cases s
    · have h := diagonal_0_1 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_1 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_1 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      have hc := congrArg star hc
      simp only [star_add,star_mul',star_star,star_div₀,star_ofNat] at hc
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have h := diagonal_1_1 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
  · fin_cases r <;> fin_cases s
    · have h := diagonal_0_2 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_2 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_2 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      have hc := congrArg star hc
      simp only [star_add,star_mul',star_star,star_div₀,star_ofNat] at hc
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have h := diagonal_1_2 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
  · fin_cases r <;> fin_cases s
    · have h := diagonal_0_3 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_3 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_3 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      have hc := congrArg star hc
      simp only [star_add,star_mul',star_star,star_div₀,star_ofNat] at hc
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have h := diagonal_1_3 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
  · fin_cases r <;> fin_cases s
    · have h := diagonal_0_4 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_4 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_4 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      have hc := congrArg star hc
      simp only [star_add,star_mul',star_star,star_div₀,star_ofNat] at hc
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have h := diagonal_1_4 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
  · fin_cases r <;> fin_cases s
    · have h := diagonal_0_5 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_5 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have hc := off_diagonal_5 c d Dg_w0 Dg_w6 Dg_w5 Dg_w11 Dg_w4 Dg_w10 Dg_w3 Dg_w9 Dg_w2 Dg_w8 Dg_w1 Dg_w7
      have hc := congrArg star hc
      simp only [star_add,star_mul',star_star,star_div₀,star_ofNat] at hc
      norm_num at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc
    · have h := diagonal_1_5 _ _ hm
      norm_num [nativeBottom,nativeTop] at h
      have hc := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at hc
      simp only [Complex.normSq_eq_conj_mul_self] at hc
      norm_num [outer,CBlock,DBlock,bottom,top,rho,R,Fin.sum_univ_succ,Fin.succ]
      linear_combination hc

theorem physical_norms_and_reflection (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ i, (∑ r : Fin 2, Complex.normSq (CBlock c i r))=R i ∧
      (∑ r : Fin 2, Complex.normSq (DBlock d i r))=R i) ∧
    (∀ i, outer (CBlock c i)+outer (DBlock d i)=(2*(R i : ℂ)) • rho c) := by
  have hm : ActualMoments c d := moments c d hc hd hnc hnd hkl
  refine ⟨block_norms c d hm,?_⟩
  intro i
  exact matrix_reflection c d hm
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w0 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w6 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w5 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w11 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w4 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w10 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w3 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w9 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w2 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w8 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w1 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef0 w7 (by decide))
    i

theorem positive_R : ∀ i, 0<R i := by intro i; fin_cases i <;> norm_num [R]

theorem physical_blocks_nonzero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 6) : CBlock c i≠0 ∧ DBlock d i≠0 := by
  have hn := (physical_norms_and_reflection c d hc hd hnc hnd hkl).1 i
  constructor
  · intro he
    have hx := hn.1
    rw [he] at hx
    norm_num at hx
    exact (ne_of_gt (positive_R i)) hx.symm
  · intro he
    have hx := hn.2
    rw [he] at hx
    norm_num at hx
    exact (ne_of_gt (positive_R i)) hx.symm

def near (i : Fin 3) : Fin 6 := ⟨i.val,by omega⟩
def far (j : Fin 3) : Fin 6 := ⟨j.val+3,by omega⟩
def crossFlip (i j : Fin 3) : SS.BitString 6 := SS.bxor (bottom (near i) 0) (top (far j) 0)

theorem cross_weight : ∀ i j, (⟨crossFlip i j,w0⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem zero_dressing : ∀ x : SS.BitString 6, SS.bdot w0 x=false := by decide +kernel
theorem cross_incidence : ∀ i j,
    S1.filter (fun y => SS.bxor y (crossFlip i j) ∈ S0)=
      {top (near i) 0,top (near i) 1,top (far j) 0,top (far j) 1} := by decide +kernel

theorem cross_scalar_0_0 (c d : SS.State 6 ℂ) :
    offSum c d (crossFlip ⟨0,by decide⟩ ⟨0,by decide⟩) w0=
      (∑ r : Fin 2, (star (CBlock c (far ⟨0,by decide⟩) r) * DBlock d (near ⟨0,by decide⟩) r +
        star (CBlock c (near ⟨0,by decide⟩) r) * DBlock d (far ⟨0,by decide⟩) r)) := by
  unfold offSum
  rw [cross_incidence ⟨0,by decide⟩ ⟨0,by decide⟩]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [show SS.bxor (top (near ⟨0,by decide⟩) 0) (crossFlip ⟨0,by decide⟩ ⟨0,by decide⟩)=bottom (far ⟨0,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (near ⟨0,by decide⟩) 1) (crossFlip ⟨0,by decide⟩ ⟨0,by decide⟩)=bottom (far ⟨0,by decide⟩) 1 by decide]
  rw [show SS.bxor (top (far ⟨0,by decide⟩) 0) (crossFlip ⟨0,by decide⟩ ⟨0,by decide⟩)=bottom (near ⟨0,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (far ⟨0,by decide⟩) 1) (crossFlip ⟨0,by decide⟩ ⟨0,by decide⟩)=bottom (near ⟨0,by decide⟩) 1 by decide]
  simp only [zero_dressing,SixQubit.signMul_false]
  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]
  ring

theorem cross_scalar_0_1 (c d : SS.State 6 ℂ) :
    offSum c d (crossFlip ⟨0,by decide⟩ ⟨1,by decide⟩) w0=
      (∑ r : Fin 2, (star (CBlock c (far ⟨1,by decide⟩) r) * DBlock d (near ⟨0,by decide⟩) r +
        star (CBlock c (near ⟨0,by decide⟩) r) * DBlock d (far ⟨1,by decide⟩) r)) := by
  unfold offSum
  rw [cross_incidence ⟨0,by decide⟩ ⟨1,by decide⟩]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [show SS.bxor (top (near ⟨0,by decide⟩) 0) (crossFlip ⟨0,by decide⟩ ⟨1,by decide⟩)=bottom (far ⟨1,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (near ⟨0,by decide⟩) 1) (crossFlip ⟨0,by decide⟩ ⟨1,by decide⟩)=bottom (far ⟨1,by decide⟩) 1 by decide]
  rw [show SS.bxor (top (far ⟨1,by decide⟩) 0) (crossFlip ⟨0,by decide⟩ ⟨1,by decide⟩)=bottom (near ⟨0,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (far ⟨1,by decide⟩) 1) (crossFlip ⟨0,by decide⟩ ⟨1,by decide⟩)=bottom (near ⟨0,by decide⟩) 1 by decide]
  simp only [zero_dressing,SixQubit.signMul_false]
  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]
  ring

theorem cross_scalar_0_2 (c d : SS.State 6 ℂ) :
    offSum c d (crossFlip ⟨0,by decide⟩ ⟨2,by decide⟩) w0=
      (∑ r : Fin 2, (star (CBlock c (far ⟨2,by decide⟩) r) * DBlock d (near ⟨0,by decide⟩) r +
        star (CBlock c (near ⟨0,by decide⟩) r) * DBlock d (far ⟨2,by decide⟩) r)) := by
  unfold offSum
  rw [cross_incidence ⟨0,by decide⟩ ⟨2,by decide⟩]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [show SS.bxor (top (near ⟨0,by decide⟩) 0) (crossFlip ⟨0,by decide⟩ ⟨2,by decide⟩)=bottom (far ⟨2,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (near ⟨0,by decide⟩) 1) (crossFlip ⟨0,by decide⟩ ⟨2,by decide⟩)=bottom (far ⟨2,by decide⟩) 1 by decide]
  rw [show SS.bxor (top (far ⟨2,by decide⟩) 0) (crossFlip ⟨0,by decide⟩ ⟨2,by decide⟩)=bottom (near ⟨0,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (far ⟨2,by decide⟩) 1) (crossFlip ⟨0,by decide⟩ ⟨2,by decide⟩)=bottom (near ⟨0,by decide⟩) 1 by decide]
  simp only [zero_dressing,SixQubit.signMul_false]
  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]
  ring

theorem cross_scalar_1_0 (c d : SS.State 6 ℂ) :
    offSum c d (crossFlip ⟨1,by decide⟩ ⟨0,by decide⟩) w0=
      (∑ r : Fin 2, (star (CBlock c (far ⟨0,by decide⟩) r) * DBlock d (near ⟨1,by decide⟩) r +
        star (CBlock c (near ⟨1,by decide⟩) r) * DBlock d (far ⟨0,by decide⟩) r)) := by
  unfold offSum
  rw [cross_incidence ⟨1,by decide⟩ ⟨0,by decide⟩]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [show SS.bxor (top (near ⟨1,by decide⟩) 0) (crossFlip ⟨1,by decide⟩ ⟨0,by decide⟩)=bottom (far ⟨0,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (near ⟨1,by decide⟩) 1) (crossFlip ⟨1,by decide⟩ ⟨0,by decide⟩)=bottom (far ⟨0,by decide⟩) 1 by decide]
  rw [show SS.bxor (top (far ⟨0,by decide⟩) 0) (crossFlip ⟨1,by decide⟩ ⟨0,by decide⟩)=bottom (near ⟨1,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (far ⟨0,by decide⟩) 1) (crossFlip ⟨1,by decide⟩ ⟨0,by decide⟩)=bottom (near ⟨1,by decide⟩) 1 by decide]
  simp only [zero_dressing,SixQubit.signMul_false]
  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]
  ring

theorem cross_scalar_1_1 (c d : SS.State 6 ℂ) :
    offSum c d (crossFlip ⟨1,by decide⟩ ⟨1,by decide⟩) w0=
      (∑ r : Fin 2, (star (CBlock c (far ⟨1,by decide⟩) r) * DBlock d (near ⟨1,by decide⟩) r +
        star (CBlock c (near ⟨1,by decide⟩) r) * DBlock d (far ⟨1,by decide⟩) r)) := by
  unfold offSum
  rw [cross_incidence ⟨1,by decide⟩ ⟨1,by decide⟩]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [show SS.bxor (top (near ⟨1,by decide⟩) 0) (crossFlip ⟨1,by decide⟩ ⟨1,by decide⟩)=bottom (far ⟨1,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (near ⟨1,by decide⟩) 1) (crossFlip ⟨1,by decide⟩ ⟨1,by decide⟩)=bottom (far ⟨1,by decide⟩) 1 by decide]
  rw [show SS.bxor (top (far ⟨1,by decide⟩) 0) (crossFlip ⟨1,by decide⟩ ⟨1,by decide⟩)=bottom (near ⟨1,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (far ⟨1,by decide⟩) 1) (crossFlip ⟨1,by decide⟩ ⟨1,by decide⟩)=bottom (near ⟨1,by decide⟩) 1 by decide]
  simp only [zero_dressing,SixQubit.signMul_false]
  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]
  ring

theorem cross_scalar_1_2 (c d : SS.State 6 ℂ) :
    offSum c d (crossFlip ⟨1,by decide⟩ ⟨2,by decide⟩) w0=
      (∑ r : Fin 2, (star (CBlock c (far ⟨2,by decide⟩) r) * DBlock d (near ⟨1,by decide⟩) r +
        star (CBlock c (near ⟨1,by decide⟩) r) * DBlock d (far ⟨2,by decide⟩) r)) := by
  unfold offSum
  rw [cross_incidence ⟨1,by decide⟩ ⟨2,by decide⟩]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [show SS.bxor (top (near ⟨1,by decide⟩) 0) (crossFlip ⟨1,by decide⟩ ⟨2,by decide⟩)=bottom (far ⟨2,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (near ⟨1,by decide⟩) 1) (crossFlip ⟨1,by decide⟩ ⟨2,by decide⟩)=bottom (far ⟨2,by decide⟩) 1 by decide]
  rw [show SS.bxor (top (far ⟨2,by decide⟩) 0) (crossFlip ⟨1,by decide⟩ ⟨2,by decide⟩)=bottom (near ⟨1,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (far ⟨2,by decide⟩) 1) (crossFlip ⟨1,by decide⟩ ⟨2,by decide⟩)=bottom (near ⟨1,by decide⟩) 1 by decide]
  simp only [zero_dressing,SixQubit.signMul_false]
  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]
  ring

theorem cross_scalar_2_0 (c d : SS.State 6 ℂ) :
    offSum c d (crossFlip ⟨2,by decide⟩ ⟨0,by decide⟩) w0=
      (∑ r : Fin 2, (star (CBlock c (far ⟨0,by decide⟩) r) * DBlock d (near ⟨2,by decide⟩) r +
        star (CBlock c (near ⟨2,by decide⟩) r) * DBlock d (far ⟨0,by decide⟩) r)) := by
  unfold offSum
  rw [cross_incidence ⟨2,by decide⟩ ⟨0,by decide⟩]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [show SS.bxor (top (near ⟨2,by decide⟩) 0) (crossFlip ⟨2,by decide⟩ ⟨0,by decide⟩)=bottom (far ⟨0,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (near ⟨2,by decide⟩) 1) (crossFlip ⟨2,by decide⟩ ⟨0,by decide⟩)=bottom (far ⟨0,by decide⟩) 1 by decide]
  rw [show SS.bxor (top (far ⟨0,by decide⟩) 0) (crossFlip ⟨2,by decide⟩ ⟨0,by decide⟩)=bottom (near ⟨2,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (far ⟨0,by decide⟩) 1) (crossFlip ⟨2,by decide⟩ ⟨0,by decide⟩)=bottom (near ⟨2,by decide⟩) 1 by decide]
  simp only [zero_dressing,SixQubit.signMul_false]
  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]
  ring

theorem cross_scalar_2_1 (c d : SS.State 6 ℂ) :
    offSum c d (crossFlip ⟨2,by decide⟩ ⟨1,by decide⟩) w0=
      (∑ r : Fin 2, (star (CBlock c (far ⟨1,by decide⟩) r) * DBlock d (near ⟨2,by decide⟩) r +
        star (CBlock c (near ⟨2,by decide⟩) r) * DBlock d (far ⟨1,by decide⟩) r)) := by
  unfold offSum
  rw [cross_incidence ⟨2,by decide⟩ ⟨1,by decide⟩]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [show SS.bxor (top (near ⟨2,by decide⟩) 0) (crossFlip ⟨2,by decide⟩ ⟨1,by decide⟩)=bottom (far ⟨1,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (near ⟨2,by decide⟩) 1) (crossFlip ⟨2,by decide⟩ ⟨1,by decide⟩)=bottom (far ⟨1,by decide⟩) 1 by decide]
  rw [show SS.bxor (top (far ⟨1,by decide⟩) 0) (crossFlip ⟨2,by decide⟩ ⟨1,by decide⟩)=bottom (near ⟨2,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (far ⟨1,by decide⟩) 1) (crossFlip ⟨2,by decide⟩ ⟨1,by decide⟩)=bottom (near ⟨2,by decide⟩) 1 by decide]
  simp only [zero_dressing,SixQubit.signMul_false]
  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]
  ring

theorem cross_scalar_2_2 (c d : SS.State 6 ℂ) :
    offSum c d (crossFlip ⟨2,by decide⟩ ⟨2,by decide⟩) w0=
      (∑ r : Fin 2, (star (CBlock c (far ⟨2,by decide⟩) r) * DBlock d (near ⟨2,by decide⟩) r +
        star (CBlock c (near ⟨2,by decide⟩) r) * DBlock d (far ⟨2,by decide⟩) r)) := by
  unfold offSum
  rw [cross_incidence ⟨2,by decide⟩ ⟨2,by decide⟩]
  rw [Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  rw [show SS.bxor (top (near ⟨2,by decide⟩) 0) (crossFlip ⟨2,by decide⟩ ⟨2,by decide⟩)=bottom (far ⟨2,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (near ⟨2,by decide⟩) 1) (crossFlip ⟨2,by decide⟩ ⟨2,by decide⟩)=bottom (far ⟨2,by decide⟩) 1 by decide]
  rw [show SS.bxor (top (far ⟨2,by decide⟩) 0) (crossFlip ⟨2,by decide⟩ ⟨2,by decide⟩)=bottom (near ⟨2,by decide⟩) 0 by decide]
  rw [show SS.bxor (top (far ⟨2,by decide⟩) 1) (crossFlip ⟨2,by decide⟩ ⟨2,by decide⟩)=bottom (near ⟨2,by decide⟩) 1 by decide]
  simp only [zero_dressing,SixQubit.signMul_false]
  norm_num [CBlock,DBlock,bottom,top,near,far,Fin.sum_univ_succ,Fin.succ]
  ring

theorem physical_complete_cross (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i j : Fin 3) :
    (∑ r : Fin 2, (star (CBlock c (far j) r) * DBlock d (near i) r +
      star (CBlock c (near i) r) * DBlock d (far j) r))=0 := by
  have h : offSum c d (crossFlip i j) w0=0 :=
    SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl (crossFlip i j) w0 (cross_weight i j)
  fin_cases i <;> fin_cases j
  · rw [cross_scalar_0_0] at h
    exact h
  · rw [cross_scalar_0_1] at h
    exact h
  · rw [cross_scalar_0_2] at h
    exact h
  · rw [cross_scalar_1_0] at h
    exact h
  · rw [cross_scalar_1_1] at h
    exact h
  · rw [cross_scalar_1_2] at h
    exact h
  · rw [cross_scalar_2_0] at h
    exact h
  · rw [cross_scalar_2_1] at h
    exact h
  · rw [cross_scalar_2_2] at h
    exact h

def mixed (v w : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := fun r s => v r * star (w s)
def pairIndex (i : Fin 2) : Fin 6 := ⟨i.val+1,by omega⟩
theorem physical_rankone_pairs (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 2) :
    mixed (DBlock d 0) (CBlock c (pairIndex i))+
      mixed (DBlock d (pairIndex i)) (CBlock c 0)=0 := by
  ext r s
  fin_cases i <;> fin_cases r <;> fin_cases s
  · have h := xr1_00 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w6 (by decide))
    simpa [mixed,CBlock,DBlock,bottom,top,pairIndex,add_comm] using h
  · have h := xr1_01 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w6 (by decide))
    simpa [mixed,CBlock,DBlock,bottom,top,pairIndex,add_comm] using h
  · have h := xr1_10 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w6 (by decide))
    simpa [mixed,CBlock,DBlock,bottom,top,pairIndex,add_comm] using h
  · have h := xr1_11 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w6 (by decide))
    simpa [mixed,CBlock,DBlock,bottom,top,pairIndex,add_comm] using h
  · have h := xr2_00 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w6 (by decide))
    simpa [mixed,CBlock,DBlock,bottom,top,pairIndex,add_comm] using h
  · have h := xr2_01 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w6 (by decide))
    simpa [mixed,CBlock,DBlock,bottom,top,pairIndex,add_comm] using h
  · have h := xr2_10 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w6 (by decide))
    simpa [mixed,CBlock,DBlock,bottom,top,pairIndex,add_comm] using h
  · have h := xr2_11 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w0 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w6 (by decide))
    simpa [mixed,CBlock,DBlock,bottom,top,pairIndex,add_comm] using h

def RankOneRows1 (c d : SS.State 6 ℂ) : Prop :=
  offSum c d ef1 w0=0 ∧ offSum c d ef1 w6=0 ∧
  offSum c d ef2 w0=0 ∧ offSum c d ef2 w6=0

theorem rankone_rows_iff_1 (c d : SS.State 6 ℂ) : RankOneRows1 c d ↔
    mixed (DBlock d 0) (CBlock c ⟨1,by decide⟩)+
      mixed (DBlock d ⟨1,by decide⟩) (CBlock c 0)=0 := by
  constructor
  · rintro ⟨h0,h6,k0,k6⟩
    ext r s
    fin_cases r <;> fin_cases s
    · have he := xr1_00 c d h0 h6
      simpa [mixed,CBlock,DBlock,bottom,top,add_comm] using he
    · have he := xr1_01 c d k0 k6
      simpa [mixed,CBlock,DBlock,bottom,top,add_comm] using he
    · have he := xr1_10 c d k0 k6
      simpa [mixed,CBlock,DBlock,bottom,top,add_comm] using he
    · have he := xr1_11 c d h0 h6
      simpa [mixed,CBlock,DBlock,bottom,top,add_comm] using he
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    norm_num [mixed,CBlock,DBlock,bottom,top] at h00 h01 h10 h11
    unfold RankOneRows1
    refine ⟨?_,?_,?_,?_⟩
    · rw [ex1_w0]
      norm_num
      linear_combination h00+h11
    · rw [ex1_w6]
      norm_num
      linear_combination h00-h11
    · rw [ex2_w0]
      norm_num
      linear_combination h01+h10
    · rw [ex2_w6]
      norm_num
      linear_combination h01-h10

def RankOneRows2 (c d : SS.State 6 ℂ) : Prop :=
  offSum c d ef3 w0=0 ∧ offSum c d ef3 w6=0 ∧
  offSum c d ef4 w0=0 ∧ offSum c d ef4 w6=0

theorem rankone_rows_iff_2 (c d : SS.State 6 ℂ) : RankOneRows2 c d ↔
    mixed (DBlock d 0) (CBlock c ⟨2,by decide⟩)+
      mixed (DBlock d ⟨2,by decide⟩) (CBlock c 0)=0 := by
  constructor
  · rintro ⟨h0,h6,k0,k6⟩
    ext r s
    fin_cases r <;> fin_cases s
    · have he := xr2_00 c d h0 h6
      simpa [mixed,CBlock,DBlock,bottom,top,add_comm] using he
    · have he := xr2_01 c d k0 k6
      simpa [mixed,CBlock,DBlock,bottom,top,add_comm] using he
    · have he := xr2_10 c d k0 k6
      simpa [mixed,CBlock,DBlock,bottom,top,add_comm] using he
    · have he := xr2_11 c d h0 h6
      simpa [mixed,CBlock,DBlock,bottom,top,add_comm] using he
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    norm_num [mixed,CBlock,DBlock,bottom,top] at h00 h01 h10 h11
    unfold RankOneRows2
    refine ⟨?_,?_,?_,?_⟩
    · rw [ex3_w0]
      norm_num
      linear_combination h00+h11
    · rw [ex3_w6]
      norm_num
      linear_combination h00-h11
    · rw [ex4_w0]
      norm_num
      linear_combination h01+h10
    · rw [ex4_w6]
      norm_num
      linear_combination h01-h10

def evaluation (F : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) : ℂ := Matrix.trace (F*outer v)

theorem evaluation_formula (F : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    evaluation F v=(∑ r : Fin 2, ∑ s : Fin 2, star (v r)*F r s*v s) := by
  simp only [evaluation,Matrix.trace,Matrix.diag,Matrix.mul_apply,outer]
  simp only [Fin.sum_univ_two]
  ring

theorem scalar_reflection_of_matrix (c d : SS.State 6 ℂ)
    (h : ∀ i, outer (CBlock c i)+outer (DBlock d i)=(2*(R i : ℂ)) • rho c)
    (F : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 6) :
    evaluation F (CBlock c i)+evaluation F (DBlock d i)=
      2*(R i : ℂ)*(∑ j, evaluation F (CBlock c j)) := by
  have he := congrArg (fun A => Matrix.trace (F*A)) (h i)
  simpa [evaluation,rho,Matrix.mul_add,Matrix.mul_sum,Matrix.mul_smul,
    Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul] using he

def entryMatrix (r s : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i=s ∧ j=r then 1 else 0

theorem matrix_pairings_iff (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    A=B ↔ ∀ F : Matrix (Fin 2) (Fin 2) ℂ, Matrix.trace (F*A)=Matrix.trace (F*B) := by
  constructor
  · intro h F; rw [h]
  · intro h
    ext r s
    have he := h (entryMatrix r s)
    fin_cases r <;> fin_cases s <;>
      norm_num [entryMatrix,Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_succ,Fin.succ] at he ⊢ <;> exact he

theorem matrix_reflection_iff (c d : SS.State 6 ℂ) :
    (∀ i, outer (CBlock c i)+outer (DBlock d i)=(2*(R i : ℂ)) • rho c) ↔
    (∀ F : Matrix (Fin 2) (Fin 2) ℂ, ∀ i,
      evaluation F (CBlock c i)+evaluation F (DBlock d i)=
        2*(R i : ℂ)*(∑ j, evaluation F (CBlock c j))) := by
  constructor
  · intro h F i
    exact scalar_reflection_of_matrix c d h F i
  · intro h i
    apply (matrix_pairings_iff _ _).2
    intro F
    simpa [evaluation,rho,Matrix.mul_add,Matrix.mul_sum,Matrix.mul_smul,
      Matrix.trace_add,Matrix.trace_sum,Matrix.trace_smul] using h F i

end
end MainTheory.Orbit33PrintedBlocks
