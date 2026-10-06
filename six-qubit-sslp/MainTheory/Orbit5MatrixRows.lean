import MainTheory.Orbit5Displays
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit5MatrixRows
open scoped Matrix BigOperators
open SixQubit.Orbit5 SixQubit.Trace5 MainTheory.Orbit5PhysicalRowData MainTheory.Orbit5Displays
noncomputable section
def bottomVector (c : SS.State 6 ℂ) : Fin 4 → Fin 4 → ℂ := ![aa1 c,aa2 c,aa3 c,aa4 c]
def topVector (d : SS.State 6 ℂ) : Fin 4 → Fin 4 → ℂ := ![bb1 d,bb2 d,bb3 d,bb4 d]
def firstCross (c d : SS.State 6 ℂ) (i : Fin 4) :=
  traceSecond (topVector d i) (uu c)+traceSecond (vv d) (bottomVector c i)
def secondCross (c d : SS.State 6 ℂ) (i : Fin 4) :=
  traceFirst (topVector d i) (uu c)+traceFirst (vv d) (bottomVector c i)
def row4 : Fin 4 → Fin 2 := ![0,0,1,1]
def col4 : Fin 4 → Fin 2 := ![0,1,0,1]
def actFirst (F : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun k => ∑ j : Fin 2,F (row4 k) j*x (coord j (col4 k))
def actSecond (F : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun k => ∑ j : Fin 2,F (col4 k) j*x (coord (row4 k) j)

theorem first_contraction (F : Matrix (Fin 2) (Fin 2) ℂ) (u v a b : Fin 4 → ℂ) :
    ip u (actFirst F b)+ip a (actFirst F v)=
      Matrix.trace (F*(traceSecond b u+traceSecond v a)) := by
  simp only [ip,actFirst,traceSecond,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.add_apply,Fin.sum_univ_two]
  change star (u 0)*(F 0 0*b 0+F 0 1*b 2)+star (u 1)*(F 0 0*b 1+F 0 1*b 3)+star (u 2)*(F 1 0*b 0+F 1 1*b 2)+star (u 3)*(F 1 0*b 1+F 1 1*b 3)+(star (a 0)*(F 0 0*v 0+F 0 1*v 2)+star (a 1)*(F 0 0*v 1+F 0 1*v 3)+star (a 2)*(F 1 0*v 0+F 1 1*v 2)+star (a 3)*(F 1 0*v 1+F 1 1*v 3))=(F 0 0*(b 0*star (u 0)+b 1*star (u 1)+(v 0*star (a 0)+v 1*star (a 1)))+F 0 1*(b 2*star (u 0)+b 3*star (u 1)+(v 2*star (a 0)+v 3*star (a 1))))+(F 1 0*(b 0*star (u 2)+b 1*star (u 3)+(v 0*star (a 2)+v 1*star (a 3)))+F 1 1*(b 2*star (u 2)+b 3*star (u 3)+(v 2*star (a 2)+v 3*star (a 3))))
  ring

theorem second_contraction (F : Matrix (Fin 2) (Fin 2) ℂ) (u v a b : Fin 4 → ℂ) :
    ip u (actSecond F b)+ip a (actSecond F v)=
      Matrix.trace (F*(traceFirst b u+traceFirst v a)) := by
  simp only [ip,actSecond,traceFirst,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.add_apply,Fin.sum_univ_two]
  change star (u 0)*(F 0 0*b 0+F 0 1*b 1)+star (u 1)*(F 1 0*b 0+F 1 1*b 1)+star (u 2)*(F 0 0*b 2+F 0 1*b 3)+star (u 3)*(F 1 0*b 2+F 1 1*b 3)+(star (a 0)*(F 0 0*v 0+F 0 1*v 1)+star (a 1)*(F 1 0*v 0+F 1 1*v 1)+star (a 2)*(F 0 0*v 2+F 0 1*v 3)+star (a 3)*(F 1 0*v 2+F 1 1*v 3))=(F 0 0*(b 0*star (u 0)+b 2*star (u 2)+(v 0*star (a 0)+v 2*star (a 2)))+F 0 1*(b 1*star (u 0)+b 3*star (u 2)+(v 1*star (a 0)+v 3*star (a 2))))+(F 1 0*(b 0*star (u 1)+b 2*star (u 3)+(v 0*star (a 1)+v 2*star (a 3)))+F 1 1*(b 1*star (u 1)+b 3*star (u 3)+(v 1*star (a 1)+v 3*star (a 3))))
  ring

theorem first_cross_0_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    firstCross c d 0=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  ext r t
  fin_cases r <;> fin_cases t
  all_goals simp only [firstCross,traceSecond,Matrix.add_apply,Matrix.zero_apply,Fin.sum_univ_two]
  · change bb1 d 0*star (uu c 0)+bb1 d 1*star (uu c 1)+(vv d 0*star (aa1 c 0)+vv d 1*star (aa1 c 1))=0
    linear_combination h21
  · change bb1 d 0*star (uu c 2)+bb1 d 1*star (uu c 3)+(vv d 0*star (aa1 c 2)+vv d 1*star (aa1 c 3))=0
    linear_combination h22
  · change bb1 d 2*star (uu c 0)+bb1 d 3*star (uu c 1)+(vv d 2*star (aa1 c 0)+vv d 3*star (aa1 c 1))=0
    linear_combination h23
  · change bb1 d 2*star (uu c 2)+bb1 d 3*star (uu c 3)+(vv d 2*star (aa1 c 2)+vv d 3*star (aa1 c 3))=0
    linear_combination h24

theorem second_cross_0_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    secondCross c d 0=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  ext r t
  fin_cases r <;> fin_cases t
  all_goals simp only [secondCross,traceFirst,Matrix.add_apply,Matrix.zero_apply,Fin.sum_univ_two]
  · change bb1 d 0*star (uu c 0)+bb1 d 2*star (uu c 2)+(vv d 0*star (aa1 c 0)+vv d 2*star (aa1 c 2))=0
    linear_combination h25
  · change bb1 d 0*star (uu c 1)+bb1 d 2*star (uu c 3)+(vv d 0*star (aa1 c 1)+vv d 2*star (aa1 c 3))=0
    linear_combination h26
  · change bb1 d 1*star (uu c 0)+bb1 d 3*star (uu c 2)+(vv d 1*star (aa1 c 0)+vv d 3*star (aa1 c 2))=0
    linear_combination h27
  · change bb1 d 1*star (uu c 1)+bb1 d 3*star (uu c 3)+(vv d 1*star (aa1 c 1)+vv d 3*star (aa1 c 3))=0
    linear_combination h28

theorem first_cross_1_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    firstCross c d 1=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  ext r t
  fin_cases r <;> fin_cases t
  all_goals simp only [firstCross,traceSecond,Matrix.add_apply,Matrix.zero_apply,Fin.sum_univ_two]
  · change bb2 d 0*star (uu c 0)+bb2 d 1*star (uu c 1)+(vv d 0*star (aa2 c 0)+vv d 1*star (aa2 c 1))=0
    linear_combination h29
  · change bb2 d 0*star (uu c 2)+bb2 d 1*star (uu c 3)+(vv d 0*star (aa2 c 2)+vv d 1*star (aa2 c 3))=0
    linear_combination h30
  · change bb2 d 2*star (uu c 0)+bb2 d 3*star (uu c 1)+(vv d 2*star (aa2 c 0)+vv d 3*star (aa2 c 1))=0
    linear_combination h31
  · change bb2 d 2*star (uu c 2)+bb2 d 3*star (uu c 3)+(vv d 2*star (aa2 c 2)+vv d 3*star (aa2 c 3))=0
    linear_combination h32

theorem second_cross_1_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    secondCross c d 1=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  ext r t
  fin_cases r <;> fin_cases t
  all_goals simp only [secondCross,traceFirst,Matrix.add_apply,Matrix.zero_apply,Fin.sum_univ_two]
  · change bb2 d 0*star (uu c 0)+bb2 d 2*star (uu c 2)+(vv d 0*star (aa2 c 0)+vv d 2*star (aa2 c 2))=0
    linear_combination h33
  · change bb2 d 0*star (uu c 1)+bb2 d 2*star (uu c 3)+(vv d 0*star (aa2 c 1)+vv d 2*star (aa2 c 3))=0
    linear_combination h34
  · change bb2 d 1*star (uu c 0)+bb2 d 3*star (uu c 2)+(vv d 1*star (aa2 c 0)+vv d 3*star (aa2 c 2))=0
    linear_combination h35
  · change bb2 d 1*star (uu c 1)+bb2 d 3*star (uu c 3)+(vv d 1*star (aa2 c 1)+vv d 3*star (aa2 c 3))=0
    linear_combination h36

theorem first_cross_2_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    firstCross c d 2=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  ext r t
  fin_cases r <;> fin_cases t
  all_goals simp only [firstCross,traceSecond,Matrix.add_apply,Matrix.zero_apply,Fin.sum_univ_two]
  · change bb3 d 0*star (uu c 0)+bb3 d 1*star (uu c 1)+(vv d 0*star (aa3 c 0)+vv d 1*star (aa3 c 1))=0
    linear_combination h37
  · change bb3 d 0*star (uu c 2)+bb3 d 1*star (uu c 3)+(vv d 0*star (aa3 c 2)+vv d 1*star (aa3 c 3))=0
    linear_combination h38
  · change bb3 d 2*star (uu c 0)+bb3 d 3*star (uu c 1)+(vv d 2*star (aa3 c 0)+vv d 3*star (aa3 c 1))=0
    linear_combination h39
  · change bb3 d 2*star (uu c 2)+bb3 d 3*star (uu c 3)+(vv d 2*star (aa3 c 2)+vv d 3*star (aa3 c 3))=0
    linear_combination h40

theorem second_cross_2_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    secondCross c d 2=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  ext r t
  fin_cases r <;> fin_cases t
  all_goals simp only [secondCross,traceFirst,Matrix.add_apply,Matrix.zero_apply,Fin.sum_univ_two]
  · change bb3 d 0*star (uu c 0)+bb3 d 2*star (uu c 2)+(vv d 0*star (aa3 c 0)+vv d 2*star (aa3 c 2))=0
    linear_combination h41
  · change bb3 d 0*star (uu c 1)+bb3 d 2*star (uu c 3)+(vv d 0*star (aa3 c 1)+vv d 2*star (aa3 c 3))=0
    linear_combination h42
  · change bb3 d 1*star (uu c 0)+bb3 d 3*star (uu c 2)+(vv d 1*star (aa3 c 0)+vv d 3*star (aa3 c 2))=0
    linear_combination h43
  · change bb3 d 1*star (uu c 1)+bb3 d 3*star (uu c 3)+(vv d 1*star (aa3 c 1)+vv d 3*star (aa3 c 3))=0
    linear_combination h44

theorem first_cross_3_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    firstCross c d 3=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  ext r t
  fin_cases r <;> fin_cases t
  all_goals simp only [firstCross,traceSecond,Matrix.add_apply,Matrix.zero_apply,Fin.sum_univ_two]
  · change bb4 d 0*star (uu c 0)+bb4 d 1*star (uu c 1)+(vv d 0*star (aa4 c 0)+vv d 1*star (aa4 c 1))=0
    linear_combination h45
  · change bb4 d 0*star (uu c 2)+bb4 d 1*star (uu c 3)+(vv d 0*star (aa4 c 2)+vv d 1*star (aa4 c 3))=0
    linear_combination h46
  · change bb4 d 2*star (uu c 0)+bb4 d 3*star (uu c 1)+(vv d 2*star (aa4 c 0)+vv d 3*star (aa4 c 1))=0
    linear_combination h47
  · change bb4 d 2*star (uu c 2)+bb4 d 3*star (uu c 3)+(vv d 2*star (aa4 c 2)+vv d 3*star (aa4 c 3))=0
    linear_combination h48

theorem second_cross_3_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    secondCross c d 3=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  ext r t
  fin_cases r <;> fin_cases t
  all_goals simp only [secondCross,traceFirst,Matrix.add_apply,Matrix.zero_apply,Fin.sum_univ_two]
  · change bb4 d 0*star (uu c 0)+bb4 d 2*star (uu c 2)+(vv d 0*star (aa4 c 0)+vv d 2*star (aa4 c 2))=0
    linear_combination h49
  · change bb4 d 0*star (uu c 1)+bb4 d 2*star (uu c 3)+(vv d 0*star (aa4 c 1)+vv d 2*star (aa4 c 3))=0
    linear_combination h50
  · change bb4 d 1*star (uu c 0)+bb4 d 3*star (uu c 2)+(vv d 1*star (aa4 c 0)+vv d 3*star (aa4 c 2))=0
    linear_combination h51
  · change bb4 d 1*star (uu c 1)+bb4 d 3*star (uu c 3)+(vv d 1*star (aa4 c 1)+vv d 3*star (aa4 c 3))=0
    linear_combination h52

theorem physical_cross_matrices (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 4) :
    firstCross c d i=0 ∧ secondCross c d i=0 := by
  have h := physical_row_data c d hc hd hnc hnd hkl
  fin_cases i
  · exact ⟨first_cross_0_of_data c d h,second_cross_0_of_data c d h⟩
  · exact ⟨first_cross_1_of_data c d h,second_cross_1_of_data c d h⟩
  · exact ⟨first_cross_2_of_data c d h,second_cross_2_of_data c d h⟩
  · exact ⟨first_cross_3_of_data c d h,second_cross_3_of_data c d h⟩

theorem physical_matrix_flips (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (hvu : vv d=uu c)
    (i : Fin 4) (F : Matrix (Fin 2) (Fin 2) ℂ) :
    (ip (uu c) (actFirst F (topVector d i))+ip (bottomVector c i) (actFirst F (uu c))=0) ∧
    (ip (uu c) (actSecond F (topVector d i))+ip (bottomVector c i) (actSecond F (uu c))=0) := by
  obtain ⟨h1,h2⟩ := physical_cross_matrices c d hc hd hnc hnd hkl i
  have hfirst : ip (uu c) (actFirst F (topVector d i))+
      ip (bottomVector c i) (actFirst F (vv d))=0 := by
    rw [first_contraction]
    change Matrix.trace (F*firstCross c d i)=0
    rw [h1,Matrix.mul_zero,Matrix.trace_zero]
  have hsecond : ip (uu c) (actSecond F (topVector d i))+
      ip (bottomVector c i) (actSecond F (vv d))=0 := by
    rw [second_contraction]
    change Matrix.trace (F*secondCross c d i)=0
    rw [h2,Matrix.mul_zero,Matrix.trace_zero]
  simpa only [hvu] using And.intro hfirst hsecond

end
end MainTheory.Orbit5MatrixRows
