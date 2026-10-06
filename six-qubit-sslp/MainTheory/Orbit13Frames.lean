import MainTheory.Orbit13BlockData
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit13Frames
open scoped BigOperators Matrix
open SixQubit.Orbit13 MainTheory.Orbit13BlockData
noncomputable section
def R : Fin 4 → SS.BitString 3 := ![![false,false,false],![false,true,true],
  ![true,false,true],![true,true,false]]
def pack (a : Bool) (r : Fin 4) (h : Bool) : SS.BitString 6 :=
  ![a,R r 0,R r 1,R r 2,h,if r=0 then h else !h]
def flipLast (x : SS.BitString 6) : SS.BitString 6 := ![x 0,x 1,x 2,x 3,x 4,!x 5]
def bottomWords : Fin 8 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7]
def bottomWordsOne : Fin 8 → SS.BitString 6 := ![y8,y9,y10,y11,y12,y13,y14,y15]
def topWords : Fin 8 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7]
def topWordsOne : Fin 8 → SS.BitString 6 := ![z8,z9,z10,z11,z12,z13,z14,z15]
def index (r : Fin 4) (h : Fin 2) : Fin 8 := ⟨2*r.val+h.val,by omega⟩
def bottomSpinor (c : SS.State 6 ℂ) (r : Fin 4) (h : Fin 2) : Fin 2 → ℂ :=
  ![c (bottomWords (index r h)),c (bottomWordsOne (index r h))]
def topSpinor (d : SS.State 6 ℂ) (r : Fin 4) (h : Fin 2) : Fin 2 → ℂ :=
  ![d (topWords (index r h)),d (topWordsOne (index r h))]
def character (s : SS.BitString 3) (j : Fin 3) : ℚ := if s j then -1 else 1
def pointProjector (r s : Fin 4) : ℚ := (1+∑ j : Fin 3,character (R r) j*character (R s) j)/4
theorem literal_R : Finset.univ.image R={![false,false,false],![false,true,true],
    ![true,false,true],![true,true,false]} := by decide +kernel
theorem literal_fibers :
    S0=Finset.univ.image (fun p : Bool × Fin 4 × Bool => pack p.1 p.2.1 p.2.2) ∧
    S1=Finset.univ.image (fun p : Bool × Fin 4 × Bool => flipLast (pack p.1 p.2.1 p.2.2)) := by decide +kernel
theorem bottom_coordinates : ∀ (r : Fin 4) (h a : Fin 2),pack (a=1) r (h=1)=
    (if a=0 then bottomWords (index r h) else bottomWordsOne (index r h)) := by decide +kernel
theorem top_coordinates : ∀ (r : Fin 4) (h a : Fin 2),flipLast (pack (a=1) r (h=1))=
    (if a=0 then topWords (index r h) else topWordsOne (index r h)) := by decide +kernel
theorem projector_checked : ∀ r s : Fin 4,pointProjector r s=(if r=s then 1 else 0) := by decide +kernel
def bottomFrame (c : SS.State 6 ℂ) (r : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ h : Fin 2,Matrix.vecMulVec (bottomSpinor c r h) (star (bottomSpinor c r h))
def topFrame (d : SS.State 6 ℂ) (r : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ h : Fin 2,Matrix.vecMulVec (topSpinor d r h) (star (topSpinor d r h))
theorem orthogonality_of_data (c d : SS.State 6 ℂ) (h : BlockData c d)
    (r : Fin 4) (i j : Fin 2) : star (bottomSpinor c r i) ⬝ᵥ topSpinor d r j=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27⟩ := h
  fin_cases r <;> fin_cases i <;> fin_cases j
  all_goals norm_num [bottomSpinor,topSpinor,bottomWords,bottomWordsOne,topWords,topWordsOne,
    index,dotProduct,Fin.sum_univ_two,Pi.star_apply]
  all_goals assumption
theorem frame_of_data (c d : SS.State 6 ℂ) (h : BlockData c d) (r : Fin 4) :
    bottomFrame c r=topFrame d r := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27⟩ := h
  have c20 := congrArg (fun x : ℝ => (x : ℂ)) h20
  push_cast at c20
  simp only [Complex.normSq_eq_conj_mul_self] at c20
  have c21 := congrArg (fun x : ℝ => (x : ℂ)) h21
  push_cast at c21
  simp only [Complex.normSq_eq_conj_mul_self] at c21
  have c22 := congrArg (fun x : ℝ => (x : ℂ)) h22
  push_cast at c22
  simp only [Complex.normSq_eq_conj_mul_self] at c22
  have c23 := congrArg (fun x : ℝ => (x : ℂ)) h23
  push_cast at c23
  simp only [Complex.normSq_eq_conj_mul_self] at c23
  have c24 := congrArg (fun x : ℝ => (x : ℂ)) h24
  push_cast at c24
  simp only [Complex.normSq_eq_conj_mul_self] at c24
  have c25 := congrArg (fun x : ℝ => (x : ℂ)) h25
  push_cast at c25
  simp only [Complex.normSq_eq_conj_mul_self] at c25
  have c26 := congrArg (fun x : ℝ => (x : ℂ)) h26
  push_cast at c26
  simp only [Complex.normSq_eq_conj_mul_self] at c26
  have c27 := congrArg (fun x : ℝ => (x : ℂ)) h27
  push_cast at c27
  simp only [Complex.normSq_eq_conj_mul_self] at c27
  have s4 := congrArg star h4
  have s9 := congrArg star h9
  have s14 := congrArg star h14
  have s19 := congrArg star h19
  fin_cases r <;> ext a b <;> fin_cases a <;> fin_cases b
  all_goals norm_num [bottomFrame,topFrame,bottomSpinor,topSpinor,bottomWords,bottomWordsOne,
    topWords,topWordsOne,index,Matrix.sum_apply,Matrix.vecMulVec_apply,Pi.star_apply,Fin.sum_univ_two]
    at c20 c21 c22 c23 c24 c25 c26 c27 h4 s4 h9 s9 h14 s14 h19 s19 ⊢
  all_goals simp only [starRingEnd_apply] at c20 c21 c22 c23 c24 c25 c26 c27 h4 s4 h9 s9 h14 s14 h19 s19 ⊢
  · linear_combination c20
  · linear_combination h4
  · linear_combination s4
  · linear_combination c21
  · linear_combination c22
  · linear_combination h9
  · linear_combination s9
  · linear_combination c23
  · linear_combination c24
  · linear_combination h14
  · linear_combination s14
  · linear_combination c25
  · linear_combination c26
  · linear_combination h19
  · linear_combination s19
  · linear_combination c27
theorem frame_product_zero (v w : Fin 2 → Fin 2 → ℂ)
    (h : ∀ i j,star (v i) ⬝ᵥ w j=0) :
    (∑ i : Fin 2,Matrix.vecMulVec (v i) (star (v i)))*
      (∑ j : Fin 2,Matrix.vecMulVec (w j) (star (w j)))=0 := by
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp only [dotProduct,Fin.sum_univ_two,Pi.star_apply] at h00 h01 h10 h11
  ext a b
  simp only [Fin.sum_univ_two,Matrix.mul_apply,Matrix.add_apply,Matrix.vecMulVec_apply,
    Pi.star_apply,Matrix.zero_apply]
  linear_combination (v 0 a*star (w 0 b))*h00+(v 0 a*star (w 1 b))*h01+
    (v 1 a*star (w 0 b))*h10+(v 1 a*star (w 1 b))*h11
theorem physical_frames (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (r : Fin 4) :
    (∀ i j,star (bottomSpinor c r i) ⬝ᵥ topSpinor d r j=0) ∧
    bottomFrame c r=topFrame d r ∧ bottomFrame c r*topFrame d r=0 := by
  have h := physical_block_data c d hc hd hnc hnd hkl
  have ho := orthogonality_of_data c d h r
  exact ⟨ho,frame_of_data c d h r,frame_product_zero _ _ ho⟩
end
end MainTheory.Orbit13Frames
