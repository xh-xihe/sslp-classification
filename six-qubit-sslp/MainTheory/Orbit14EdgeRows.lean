import MainTheory.Orbit14ParityFrames
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit14EdgeRows
open scoped BigOperators Matrix
open SixQubit.Orbit14 MainTheory.Orbit14ParityFrames
noncomputable section
def middleAdjacent (z w : SS.BitString 4) : Prop := z 0=w 0 ∧
  (List.ofFn (fun i : Fin 3 => decide (z i.succ≠w i.succ))).count true=1
theorem middle_adjacent_checked : ∀ g h : Fin 8,
    middleAdjacent (bottomLabels g) (topLabels h) ↔
      g.val/4=h.val/4 ∧ g.val%4+h.val%4≠3 := by
  unfold middleAdjacent
  decide +kernel
theorem edge_rows_of_data (c d : SS.State 6 ℂ) (h : FrameData c d)
    (g k : Fin 8) (hadj : middleAdjacent (bottomLabels g) (topLabels k)) :
    star (bottomSpinor c g) ⬝ᵥ topSpinor d k=0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩ := h
  rw [middle_adjacent_checked] at hadj
  fin_cases g <;> fin_cases k
  all_goals norm_num at hadj
  all_goals norm_num [bottomSpinor,topSpinor,bottomWords,bottomWordsOne,topWords,topWordsOne,
    dotProduct,Fin.sum_univ_two,Pi.star_apply]
  all_goals assumption
theorem physical_edge_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (g k : Fin 8)
    (hadj : middleAdjacent (bottomLabels g) (topLabels k)) :
    star (bottomSpinor c g) ⬝ᵥ topSpinor d k=0 := by
  exact edge_rows_of_data c d (physical_frame_data c d hc hd hnc hnd hkl) g k hadj
end
end MainTheory.Orbit14EdgeRows
