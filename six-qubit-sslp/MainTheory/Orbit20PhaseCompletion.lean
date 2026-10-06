import MainTheory.Orbit20DisplayCompletion
set_option autoImplicit false
namespace MainTheory.Orbit20PhaseCompletion
open scoped Matrix
open SixQubit.Orbit20 MainTheory.Orbit20PhysicalRowData MainTheory.Orbit20DisplayCompletion
noncomputable section
def relation (c d : SS.State 6 ℂ) (r i j : Fin 4) : ℂ :=
  star (c (bottomWord r i))*d (matchedTopWord r j)+
  star (c (bottomWord r j))*d (matchedTopWord r i)
def rho (c d : SS.State 6 ℂ) (r y : Fin 4) : ℂ :=
  d (matchedTopWord r y)/star (c (bottomWord r y))

theorem divide_reciprocal (a b A B : ℂ) (ha : a≠0) (hb : b≠0)
    (h : star a*B+star b*A=0) : A/star a+B/star b=0 := by
  have hsa : star a≠0 := star_ne_zero.mpr ha
  have hsb : star b≠0 := star_ne_zero.mpr hb
  field_simp
  linear_combination h

theorem relation_0_of_data (c d : SS.State 6 ℂ) (h : RowData c d)
    (i j : Fin 4) (hij : i≠j) : relation c d 0 i j=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h0
  · exact h1
  · exact h2
  · change _+_=0
    rw [add_comm]
    exact h0
  · exact (hij rfl).elim
  · exact h3
  · exact h4
  · change _+_=0
    rw [add_comm]
    exact h1
  · change _+_=0
    rw [add_comm]
    exact h3
  · exact (hij rfl).elim
  · exact h5
  · change _+_=0
    rw [add_comm]
    exact h2
  · change _+_=0
    rw [add_comm]
    exact h4
  · change _+_=0
    rw [add_comm]
    exact h5
  · exact (hij rfl).elim

theorem relation_1_of_data (c d : SS.State 6 ℂ) (h : RowData c d)
    (i j : Fin 4) (hij : i≠j) : relation c d 1 i j=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h6
  · exact h7
  · exact h8
  · change _+_=0
    rw [add_comm]
    exact h6
  · exact (hij rfl).elim
  · exact h9
  · exact h10
  · change _+_=0
    rw [add_comm]
    exact h7
  · change _+_=0
    rw [add_comm]
    exact h9
  · exact (hij rfl).elim
  · exact h11
  · change _+_=0
    rw [add_comm]
    exact h8
  · change _+_=0
    rw [add_comm]
    exact h10
  · change _+_=0
    rw [add_comm]
    exact h11
  · exact (hij rfl).elim

theorem relation_2_of_data (c d : SS.State 6 ℂ) (h : RowData c d)
    (i j : Fin 4) (hij : i≠j) : relation c d 2 i j=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h12
  · exact h13
  · exact h14
  · change _+_=0
    rw [add_comm]
    exact h12
  · exact (hij rfl).elim
  · exact h15
  · exact h16
  · change _+_=0
    rw [add_comm]
    exact h13
  · change _+_=0
    rw [add_comm]
    exact h15
  · exact (hij rfl).elim
  · exact h17
  · change _+_=0
    rw [add_comm]
    exact h14
  · change _+_=0
    rw [add_comm]
    exact h16
  · change _+_=0
    rw [add_comm]
    exact h17
  · exact (hij rfl).elim

theorem relation_3_of_data (c d : SS.State 6 ℂ) (h : RowData c d)
    (i j : Fin 4) (hij : i≠j) : relation c d 3 i j=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h18
  · exact h19
  · exact h20
  · change _+_=0
    rw [add_comm]
    exact h18
  · exact (hij rfl).elim
  · exact h21
  · exact h22
  · change _+_=0
    rw [add_comm]
    exact h19
  · change _+_=0
    rw [add_comm]
    exact h21
  · exact (hij rfl).elim
  · exact h23
  · change _+_=0
    rw [add_comm]
    exact h20
  · change _+_=0
    rw [add_comm]
    exact h22
  · change _+_=0
    rw [add_comm]
    exact h23
  · exact (hij rfl).elim

theorem relation_of_data (c d : SS.State 6 ℂ) (h : RowData c d)
    (r i j : Fin 4) (hij : i≠j) : relation c d r i j=0 := by
  fin_cases r
  exacts [relation_0_of_data c d h i j hij,relation_1_of_data c d h i j hij,
    relation_2_of_data c d h i j hij,relation_3_of_data c d h i j hij]

theorem ratio_pairs_of_data (c d : SS.State 6 ℂ) (h : RowData c d)
    (r : Fin 4) (hpos : 0<prob c r 0) (i j : Fin 4) (hij : i≠j) :
    rho c d r i+rho c d r j=0 := by
  have hn (y : Fin 4) : c (bottomWord r y)≠0 := by
    intro hz
    have hu := uniform_of_data c d h r y
    change Complex.normSq (c (bottomWord r y))=prob c r 0 at hu
    rw [hz,Complex.normSq_zero] at hu
    linarith
  exact divide_reciprocal _ _ _ _ (hn i) (hn j) (relation_of_data c d h r i j hij)

def oddTriangle : Matrix (Fin 3) (Fin 3) ℤ := ![![1,1,0],![1,0,1],![0,1,1]]
theorem triangle_determinant : oddTriangle.det=-2 := by decide +kernel
theorem triangle_rows (x y z : ℂ) (hxy : x+y=0) (hxz : x+z=0) (hyz : y+z=0) :
    (oddTriangle.map fun n => (n : ℂ)).mulVec ![x,y,z]=0 := by
  ext i
  fin_cases i
  all_goals norm_num [oddTriangle,Matrix.map_apply,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,Fin.succ]
  exacts [hxy,hxz,hyz]

theorem physical_ratio_pairs (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (r : Fin 4) (hpos : 0<prob c r 0)
    (i j : Fin 4) (hij : i≠j) : rho c d r i+rho c d r j=0 :=
  ratio_pairs_of_data c d (physical_row_data c d hc hd hnc hnd hkl) r hpos i j hij

theorem ratio_unit_of_data (c d : SS.State 6 ℂ) (h : RowData c d)
    (r : Fin 4) (hpos : 0<prob c r 0) (y : Fin 4) :
    Complex.normSq (rho c d r y)=1 := by
  have hu := uniform_of_data c d h r y
  have hn : prob c r y≠0 := by rw [hu]; exact ne_of_gt hpos
  have hm := matched_norms_of_data c d h r y
  change Complex.normSq (c (bottomWord r y))=
    Complex.normSq (d (matchedTopWord r y)) at hm
  simp only [rho,map_div₀,Complex.star_def,Complex.normSq_conj]
  rw [← hm]
  exact div_self hn

theorem physical_triangle (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (r : Fin 4) (hpos : 0<prob c r 0)
    (i j k : Fin 4) (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    (oddTriangle.map fun n => (n : ℂ)).mulVec
      ![rho c d r i,rho c d r j,rho c d r k]=0 :=
  triangle_rows _ _ _
    (physical_ratio_pairs c d hc hd hnc hnd hkl r hpos i j hij)
    (physical_ratio_pairs c d hc hd hnc hnd hkl r hpos i k hik)
    (physical_ratio_pairs c d hc hd hnc hnd hkl r hpos j k hjk)

end
end MainTheory.Orbit20PhaseCompletion
