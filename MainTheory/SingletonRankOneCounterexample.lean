import MainTheory.CodeSpec

/-! With the manuscript's KL definition, rank one detects every operator.
The unrestricted real-exponent Singleton inequality therefore needs a rank
qualification; natural-number truncated subtraction would hide this issue. -/

namespace MainTheory.SingletonRankOneCounterexample

noncomputable def state : SS.State 3 ℂ := fun x => if x=(fun _ => false) then 1 else 0

theorem normalized : SS.innerC state state=1 := by
  classical
  simp [SS.innerC,state]

noncomputable def frame : MainTheory.CodeSpec.OrthonormalFrame 3 1 where
  vec _ := state
  orthonormal i j := by
    have h : i=j := Subsingleton.elim _ _
    simpa [h] using normalized

theorem detects_all_distances (d : ℕ) : SS.HasDistance frame.vec d := by
  intro P _
  refine ⟨SS.innerC state (SS.pauliAct P state),?_⟩
  intro i j
  simp [frame,Subsingleton.elim i j]

noncomputable def code : MainTheory.CodeSpec.ExactCode 3 1 3 where
  positiveRank := by norm_num
  frame := frame
  hasDistance := detects_all_distances 3

theorem violates_unrestricted_singleton :
    ∃ _Q : MainTheory.CodeSpec.ExactCode 3 1 3,
      ¬ (1 : ℝ) ≤ (2 : ℝ)^((3 : ℤ)-2*(3-1)) := by
  exact ⟨code,by norm_num⟩

end MainTheory.SingletonRankOneCounterexample
