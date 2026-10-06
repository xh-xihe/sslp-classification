import MainTheory.Orbit6PhysicalRowData
import MainTheory.Orbit6MomentDisplays
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit6SpinorDisplays
open scoped BigOperators Matrix
open SixQubit.Orbit6 MainTheory.Orbit6MomentDisplays MainTheory.Orbit6PhysicalRowData
noncomputable section
def bIndex : Fin 5 → Fin 10 := ![5,3,2,1,0]
def cIndex : Fin 5 → Fin 10 := ![4,6,7,8,9]
def first (i : Fin 10) : Fin 20 := ⟨i.val,by omega⟩
def second (i : Fin 10) : Fin 20 := ⟨i.val+10,by omega⟩
def anchor (c : SS.State 6 ℂ) : Fin 2 → ℂ := ![c y0,c y11]
def bottomEdge (c : SS.State 6 ℂ) (e : Fin 10) : Fin 2 → ℂ :=
  ![![c y1,c y12],![c y2,c y13],![c y3,c y14],![c y4,c y15],![c y5,c y16],
    ![c y6,c y17],![c y7,c y18],![c y8,c y19],![c y9,c y20],![c y10,c y21]] e
def topSingleton (d : SS.State 6 ℂ) (i : Fin 5) : Fin 2 → ℂ :=
  ![![d z5,d z15],![d z3,d z13],![d z2,d z12],![d z1,d z11],![d z0,d z10]] i
def topComplement (d : SS.State 6 ℂ) (i : Fin 5) : Fin 2 → ℂ :=
  ![![d z4,d z14],![d z6,d z16],![d z7,d z17],![d z8,d z18],![d z9,d z19]] i
@[simp] theorem index_ne_0_1 : (0 : Fin 5)≠1 := by decide +kernel
@[simp] theorem index_ne_0_2 : (0 : Fin 5)≠2 := by decide +kernel
@[simp] theorem index_ne_0_3 : (0 : Fin 5)≠3 := by decide +kernel
@[simp] theorem index_ne_0_4 : (0 : Fin 5)≠4 := by decide +kernel
@[simp] theorem index_ne_1_0 : (1 : Fin 5)≠0 := by decide +kernel
@[simp] theorem index_ne_1_2 : (1 : Fin 5)≠2 := by decide +kernel
@[simp] theorem index_ne_1_3 : (1 : Fin 5)≠3 := by decide +kernel
@[simp] theorem index_ne_1_4 : (1 : Fin 5)≠4 := by decide +kernel
@[simp] theorem index_ne_2_0 : (2 : Fin 5)≠0 := by decide +kernel
@[simp] theorem index_ne_2_1 : (2 : Fin 5)≠1 := by decide +kernel
@[simp] theorem index_ne_2_3 : (2 : Fin 5)≠3 := by decide +kernel
@[simp] theorem index_ne_2_4 : (2 : Fin 5)≠4 := by decide +kernel
@[simp] theorem index_ne_3_0 : (3 : Fin 5)≠0 := by decide +kernel
@[simp] theorem index_ne_3_1 : (3 : Fin 5)≠1 := by decide +kernel
@[simp] theorem index_ne_3_2 : (3 : Fin 5)≠2 := by decide +kernel
@[simp] theorem index_ne_3_4 : (3 : Fin 5)≠4 := by decide +kernel
@[simp] theorem index_ne_4_0 : (4 : Fin 5)≠0 := by decide +kernel
@[simp] theorem index_ne_4_1 : (4 : Fin 5)≠1 := by decide +kernel
@[simp] theorem index_ne_4_2 : (4 : Fin 5)≠2 := by decide +kernel
@[simp] theorem index_ne_4_3 : (4 : Fin 5)≠3 := by decide +kernel
@[simp] theorem topComplement_0_0 (d : SS.State 6 ℂ) : topComplement d 0 0=d z4 := rfl
@[simp] theorem topComplement_0_1 (d : SS.State 6 ℂ) : topComplement d 0 1=d z14 := rfl
@[simp] theorem topComplement_1_0 (d : SS.State 6 ℂ) : topComplement d 1 0=d z6 := rfl
@[simp] theorem topComplement_1_1 (d : SS.State 6 ℂ) : topComplement d 1 1=d z16 := rfl
@[simp] theorem topComplement_2_0 (d : SS.State 6 ℂ) : topComplement d 2 0=d z7 := rfl
@[simp] theorem topComplement_2_1 (d : SS.State 6 ℂ) : topComplement d 2 1=d z17 := rfl
@[simp] theorem topComplement_3_0 (d : SS.State 6 ℂ) : topComplement d 3 0=d z8 := rfl
@[simp] theorem topComplement_3_1 (d : SS.State 6 ℂ) : topComplement d 3 1=d z18 := rfl
@[simp] theorem topComplement_4_0 (d : SS.State 6 ℂ) : topComplement d 4 0=d z9 := rfl
@[simp] theorem topComplement_4_1 (d : SS.State 6 ℂ) : topComplement d 4 1=d z19 := rfl
def pairing (v w : Fin 2 → ℂ) : ℂ := star (v 0)*w 0+star (v 1)*w 1
def wedge (v w : Fin 2 → ℂ) : ℂ := v 0*w 1-v 1*w 0
def edgeOuter (c d : SS.State 6 ℂ) (k : Fin 5) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ e : Fin 10,if k=(edges e).1 then
    Matrix.vecMulVec (topComplement d (edges e).2) (star (bottomEdge c e))
  else if k=(edges e).2 then
    Matrix.vecMulVec (topComplement d (edges e).1) (star (bottomEdge c e)) else 0

theorem aligned_rows_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    (∀ i,pairing (anchor c) (topSingleton d i)=0) ∧
    (∀ e,pairing (bottomEdge c e) (anchor c)=0) ∧
    (∀ i,wedge (anchor c) (topComplement d i)=0) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46⟩ := h
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i
    exacts [h0,h1,h2,h3,h4]
  · intro e
    fin_cases e
    exacts [h9,h10,h11,h12,h13,h14,h15,h16,h17,h18]
  · intro i
    fin_cases i
    exacts [h42,h43,h44,h45,h46]

theorem matrix_identity_0_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    Matrix.vecMulVec (topSingleton d 0) (star (anchor c))+edgeOuter c d 0=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46⟩ := h
  ext a b
  fin_cases a <;> fin_cases b
  all_goals norm_num [edgeOuter,edges,Matrix.add_apply,Matrix.vecMulVec_apply,
    Matrix.zero_apply,Matrix.sum_apply,anchor,topSingleton,bottomEdge,
    Pi.star_apply,Fin.sum_univ_succ,Fin.succ,Fin.reduceFinMk]
  all_goals simp only [starRingEnd_apply] at h19 h20 h21 h22 ⊢
  · linear_combination h19
  · linear_combination h21
  · linear_combination h20
  · linear_combination h22

theorem matrix_identity_1_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    Matrix.vecMulVec (topSingleton d 1) (star (anchor c))+edgeOuter c d 1=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46⟩ := h
  ext a b
  fin_cases a <;> fin_cases b
  all_goals norm_num [edgeOuter,edges,Matrix.add_apply,Matrix.vecMulVec_apply,
    Matrix.zero_apply,Matrix.sum_apply,anchor,topSingleton,bottomEdge,
    Pi.star_apply,Fin.sum_univ_succ,Fin.succ,Fin.reduceFinMk]
  all_goals simp only [starRingEnd_apply] at h23 h24 h25 h26 ⊢
  · linear_combination h23
  · linear_combination h25
  · linear_combination h24
  · linear_combination h26

theorem matrix_identity_2_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    Matrix.vecMulVec (topSingleton d 2) (star (anchor c))+edgeOuter c d 2=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46⟩ := h
  ext a b
  fin_cases a <;> fin_cases b
  all_goals norm_num [edgeOuter,edges,Matrix.add_apply,Matrix.vecMulVec_apply,
    Matrix.zero_apply,Matrix.sum_apply,anchor,topSingleton,bottomEdge,
    Pi.star_apply,Fin.sum_univ_succ,Fin.succ,Fin.reduceFinMk]
  all_goals try simp
  all_goals simp only [starRingEnd_apply] at h27 h28 h29 h30 ⊢
  · linear_combination h27
  · linear_combination h29
  · linear_combination h28
  · linear_combination h30

theorem matrix_identity_3_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    Matrix.vecMulVec (topSingleton d 3) (star (anchor c))+edgeOuter c d 3=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46⟩ := h
  ext a b
  fin_cases a <;> fin_cases b
  all_goals norm_num [edgeOuter,edges,Matrix.add_apply,Matrix.vecMulVec_apply,
    Matrix.zero_apply,Matrix.sum_apply,anchor,topSingleton,bottomEdge,
    Pi.star_apply,Fin.sum_univ_succ,Fin.succ,Fin.reduceFinMk]
  all_goals try simp
  all_goals simp only [starRingEnd_apply] at h31 h32 h33 h34 ⊢
  · linear_combination h31
  · linear_combination h33
  · linear_combination h32
  · linear_combination h34

theorem matrix_identity_4_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    Matrix.vecMulVec (topSingleton d 4) (star (anchor c))+edgeOuter c d 4=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46⟩ := h
  ext a b
  fin_cases a <;> fin_cases b
  all_goals norm_num [edgeOuter,edges,Matrix.add_apply,Matrix.vecMulVec_apply,
    Matrix.zero_apply,Matrix.sum_apply,anchor,topSingleton,bottomEdge,
    Pi.star_apply,Fin.sum_univ_succ,Fin.succ,Fin.reduceFinMk]
  all_goals try simp
  all_goals simp only [starRingEnd_apply] at h35 h36 h37 h38 ⊢
  · linear_combination h35
  · linear_combination h37
  · linear_combination h36
  · linear_combination h38

theorem matrix_identity_of_data (c d : SS.State 6 ℂ) (h : RowData c d) (k : Fin 5) :
    Matrix.vecMulVec (topSingleton d k) (star (anchor c))+edgeOuter c d k=0 := by
  fin_cases k
  exacts [matrix_identity_0_of_data c d h,matrix_identity_1_of_data c d h,matrix_identity_2_of_data c d h,matrix_identity_3_of_data c d h,matrix_identity_4_of_data c d h]

theorem physical_aligned_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ i,pairing (anchor c) (topSingleton d i)=0) ∧
    (∀ e,pairing (bottomEdge c e) (anchor c)=0) ∧
    (∀ i,wedge (anchor c) (topComplement d i)=0) :=
  aligned_rows_of_data c d (physical_row_data c d hc hd hnc hnd hkl)

theorem physical_matrix_identity (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (k : Fin 5) :
    Matrix.vecMulVec (topSingleton d k) (star (anchor c))+edgeOuter c d k=0 :=
  matrix_identity_of_data c d (physical_row_data c d hc hd hnc hnd hkl) k
end
end MainTheory.Orbit6SpinorDisplays
