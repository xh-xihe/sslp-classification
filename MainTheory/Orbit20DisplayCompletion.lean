import MainTheory.Orbit20PhysicalRowData
set_option autoImplicit false
namespace MainTheory.Orbit20DisplayCompletion
open scoped BigOperators Matrix
open SixQubit.Orbit20 MainTheory.Orbit20PhysicalRowData
noncomputable section
def bottomWord : Fin 4 → Fin 4 → SS.BitString 6 :=
  ![![y0,y1,y2,y3],![y4,y5,y6,y7],![y8,y9,y10,y11],![y12,y13,y14,y15]]
def matchedTopWord : Fin 4 → Fin 4 → SS.BitString 6 :=
  ![![z3,z2,z1,z0],![z7,z6,z5,z4],![z11,z10,z9,z8],![z15,z14,z13,z12]]
def blockPattern (r : Fin 4) : SS.BitString 3 := fun j => bottomWord r 0 (j.castAdd 3)
def tail (r y : Fin 4) : SS.BitString 3 := fun j => bottomWord r y (j.addNat 3)
def epsilon (r : Fin 4) : Bool := decide (r≠0)
def character (r y : Fin 4) (k : Fin 3) : ℝ := if tail r y k then -1 else 1
def prob (c : SS.State 6 ℂ) (r y : Fin 4) : ℝ := Complex.normSq (c (bottomWord r y))
def topProb (d : SS.State 6 ℂ) (r y : Fin 4) : ℝ := Complex.normSq (d (matchedTopWord r y))

theorem epsilon_checked : epsilon 0=false ∧ ∀ r : Fin 4,r≠0 → epsilon r=true := by decide +kernel
theorem literal_matching : ∀ r y : Fin 4,∀ k : Fin 3,
    matchedTopWord r y (k.castAdd 3)=bottomWord r y (k.castAdd 3) ∧
    matchedTopWord r y (k.addNat 3)=!(bottomWord r y (k.addNat 3)) := by decide +kernel
theorem character_balanced : ∀ r : Fin 4,∀ k : Fin 3,
    ∑ y : Fin 4,(if tail r y k then (-1 : ℤ) else 1)=0 := by decide +kernel

theorem uniform_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    ∀ r y : Fin 4,prob c r y=prob c r 0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  intro r y
  fin_cases r <;> fin_cases y
  · rfl
  · exact h40
  · exact h41
  · exact h42
  · rfl
  · exact h43
  · exact h44
  · exact h45
  · rfl
  · exact h46
  · exact h47
  · exact h48
  · rfl
  · exact h49
  · exact h50
  · exact h51

theorem matched_norms_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    ∀ r y : Fin 4,prob c r y=topProb d r y := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩ := h
  intro r y
  fin_cases r <;> fin_cases y
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29
  · exact h30
  · exact h31
  · exact h32
  · exact h33
  · exact h34
  · exact h35
  · exact h36
  · exact h37
  · exact h38
  · exact h39

theorem block_characters_of_data (c d : SS.State 6 ℂ) (h : RowData c d)
    (r : Fin 4) (k : Fin 3) : ∑ y : Fin 4,prob c r y*character r y k=0 := by
  have hu := uniform_of_data c d h
  simp_rw [hu r]
  rw [← Finset.mul_sum]
  have hb : ∑ y : Fin 4,character r y k=0 := by
    have hb := congrArg (fun z : ℤ => (z : ℝ)) (character_balanced r k)
    push_cast at hb
    simpa only [character,Int.cast_ite,Int.cast_neg,Int.cast_one] using hb
  rw [hb,mul_zero]

theorem global_characters_of_data (c d : SS.State 6 ℂ) (h : RowData c d) (k : Fin 3) :
    (∑ r : Fin 4,∑ y : Fin 4,prob c r y*character r y k)=0 ∧
    (∀ i : Fin 3,(∑ r : Fin 4,∑ y : Fin 4,
      prob c r y*(if blockPattern r i then -1 else 1)*character r y k)=0) := by
  constructor
  · simp only [block_characters_of_data c d h,Finset.sum_const_zero]
  · intro i
    apply Finset.sum_eq_zero
    intro r _
    have hb := block_characters_of_data c d h r k
    calc
      _ = (if blockPattern r i then (-1 : ℝ) else 1)*
          (∑ y : Fin 4,prob c r y*character r y k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = 0 := by rw [hb,mul_zero]

theorem physical_characters (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (k : Fin 3) :
    (∀ r : Fin 4,∑ y : Fin 4,prob c r y*character r y k=0) ∧
    (∑ r : Fin 4,∑ y : Fin 4,prob c r y*character r y k)=0 ∧
    (∀ i : Fin 3,(∑ r : Fin 4,∑ y : Fin 4,
      prob c r y*(if blockPattern r i then -1 else 1)*character r y k)=0) := by
  have h := physical_row_data c d hc hd hnc hnd hkl
  exact ⟨fun r => block_characters_of_data c d h r k,global_characters_of_data c d h k⟩

end
end MainTheory.Orbit20DisplayCompletion
