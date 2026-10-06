import MainTheory.Orbit14ParityFrames
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit14BlockFrames
open scoped BigOperators Matrix
open SixQubit.Orbit14 MainTheory.Orbit14ParityFrames
noncomputable section

def blockIndex (r : Bool) (i : Fin 4) : Fin 8 :=
  ⟨i.val+(if r then 4 else 0),by split_ifs <;> omega⟩
def bottomBlockFrame (c : SS.State 6 ℂ) (r : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 4,Matrix.vecMulVec (bottomSpinor c (blockIndex r i))
    (star (bottomSpinor c (blockIndex r i)))
def topBlockFrame (d : SS.State 6 ℂ) (r : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ i : Fin 4,Matrix.vecMulVec (topSpinor d (blockIndex r i))
    (star (topSpinor d (blockIndex r i)))
theorem block_labels : ∀ (r : Bool) (i : Fin 4),
    bottomLabels (blockIndex r i) 0=r ∧ topLabels (blockIndex r i) 0=r := by decide +kernel
theorem block_labels_exact : ∀ r : Bool,
    Finset.univ.image (fun i : Fin 4 => bottomLabels (blockIndex r i))=
      Finset.univ.filter (fun z : SS.BitString 4 => parity z=false ∧ z 0=r) ∧
    Finset.univ.image (fun i : Fin 4 => topLabels (blockIndex r i))=
      Finset.univ.filter (fun z : SS.BitString 4 => parity z=true ∧ z 0=r) := by decide +kernel
theorem block_frame_of_data (c d : SS.State 6 ℂ) (h : FrameData c d) (r : Bool) :
    bottomBlockFrame c r=topBlockFrame d r := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩ := h
  have c26 := congrArg (fun x : ℝ => (x : ℂ)) h26
  push_cast at c26
  simp only [Complex.normSq_eq_conj_mul_self] at c26
  have c27 := congrArg (fun x : ℝ => (x : ℂ)) h27
  push_cast at c27
  simp only [Complex.normSq_eq_conj_mul_self] at c27
  have c28 := congrArg (fun x : ℝ => (x : ℂ)) h28
  push_cast at c28
  simp only [Complex.normSq_eq_conj_mul_self] at c28
  have c29 := congrArg (fun x : ℝ => (x : ℂ)) h29
  push_cast at c29
  simp only [Complex.normSq_eq_conj_mul_self] at c29
  have s12 := congrArg star h12
  have s25 := congrArg star h25

  cases r <;> ext a b <;> fin_cases a <;> fin_cases b
  all_goals norm_num [bottomBlockFrame,topBlockFrame,blockIndex,bottomSpinor,topSpinor,
    bottomWords,bottomWordsOne,topWords,topWordsOne,Matrix.sum_apply,
    Matrix.vecMulVec_apply,Pi.star_apply,Fin.sum_univ_succ,Fin.succ]
    at c26 c27 c28 c29 h12 h25 s12 s25 ⊢
  all_goals simp only [starRingEnd_apply] at c26 c27 c28 c29 h12 h25 s12 s25 ⊢
  · linear_combination c26
  · linear_combination h12
  · linear_combination s12
  · linear_combination c27
  · linear_combination c28
  · linear_combination h25
  · linear_combination s25
  · linear_combination c29
theorem physical_block_frame_equality (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (r : Bool) :
    bottomBlockFrame c r=topBlockFrame d r := by
  exact block_frame_of_data c d (physical_frame_data c d hc hd hnc hnd hkl) r
end
end MainTheory.Orbit14BlockFrames
