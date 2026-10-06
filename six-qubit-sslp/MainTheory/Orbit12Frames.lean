import MainTheory.Orbit12PhysicalRowData
import MainTheory.Orbit12MomentDisplays
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit12Frames
open scoped BigOperators Matrix
open SixQubit.Orbit12 MainTheory.Orbit12PhysicalRowData
noncomputable section
def u (c : SS.State 6 ℂ) : Fin 2 → ℂ := ![c y0,c y8]
def v (c : SS.State 6 ℂ) : Fin 2 → ℂ := ![c y7,c y15]
def ut (d : SS.State 6 ℂ) : Fin 2 → ℂ := ![d z0,d z8]
def vt (d : SS.State 6 ℂ) : Fin 2 → ℂ := ![d z7,d z15]
def a (c : SS.State 6 ℂ) : Fin 6 → Fin 2 → ℂ :=
  ![![c y6,c y14],![c y5,c y13],![c y4,c y12],![c y3,c y11],![c y2,c y10],![c y1,c y9]]
def b (d : SS.State 6 ℂ) : Fin 6 → Fin 2 → ℂ :=
  ![![d z6,d z14],![d z5,d z13],![d z4,d z12],![d z3,d z11],![d z2,d z10],![d z1,d z9]]
def outer (x : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.vecMulVec x (star x)
def AHcrossBlock (c d : SS.State 6 ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.vecMulVec (ut d) (star (u c))+Matrix.vecMulVec (vt d) (star (v c))
def H0bottomFrame (c : SS.State 6 ℂ) := outer (u c)+outer (v c)
def H0topFrame (d : SS.State 6 ℂ) := ∑ e : Fin 6,outer (b d e)

theorem cross_block_of_data (c d : SS.State 6 ℂ) (h : RowData c d) : AHcrossBlock c d=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := h
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [AHcrossBlock,u,v,ut,vt,Matrix.add_apply,Matrix.vecMulVec_apply,
    Pi.star_apply,Matrix.zero_apply]
  all_goals simp only [starRingEnd_apply]
  · linear_combination h0
  · linear_combination h2
  · linear_combination h1
  · linear_combination h3

theorem H0_frame_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    H0bottomFrame c=H0topFrame d := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩ := h
  have c0 := congrArg (fun x : ℝ => (x : ℂ)) h7
  have c1 := congrArg (fun x : ℝ => (x : ℂ)) h8
  push_cast at c0 c1
  simp only [Complex.normSq_eq_conj_mul_self] at c0 c1
  have hs := congrArg star h4
  simp only [star_add,star_mul',star_star] at hs
  ext i j
  fin_cases i <;> fin_cases j
  all_goals norm_num [H0bottomFrame,H0topFrame,outer,u,v,b,Matrix.add_apply,
    Matrix.vecMulVec_apply,Matrix.sum_apply,Pi.star_apply,Fin.sum_univ_succ,Fin.succ]
  all_goals simp only [starRingEnd_apply] at c0 c1 h4 hs ⊢
  · linear_combination c0
  · linear_combination h4
  · linear_combination hs
  · linear_combination c1

theorem physical_blocks (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    AHcrossBlock c d=0 ∧ H0bottomFrame c=H0topFrame d := by
  have h := physical_row_data c d hc hd hnc hnd hkl
  exact ⟨cross_block_of_data c d h,H0_frame_of_data c d h⟩
end
end MainTheory.Orbit12Frames
