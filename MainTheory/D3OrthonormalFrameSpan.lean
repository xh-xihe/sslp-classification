import MainTheory.D3LogicalAction

/-!
# Linear independence and span comparison for stored frames

The repository's `CodeSpec.OrthonormalFrame` uses the custom finite-sum inner
product rather than mathlib's bundled inner-product-space structure.  This
file supplies the small missing bridge: its vectors are linearly independent,
its rank-two span has finrank two, and inclusion between spans of two
rank-two orthonormal frames is therefore equality.
-/

namespace MainTheory.D3OrthonormalFrameSpan

variable {n d : ℕ}

open MainTheory

noncomputable section

/-- A stored orthonormal frame is linearly independent. -/
theorem frame_linearIndependent (F : CodeSpec.OrthonormalFrame n 2) :
    LinearIndependent ℂ F.vec := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsynth : D3LogicalAction.synthesisLinear F g = 0 := by
    change (∑ k, g k • F.vec k) = 0
    exact hg
  have hg0 : g = 0 := by
    apply D3LogicalAction.synthesis_injective F
    simpa using hsynth
  exact congrFun hg0 i

/-- The span of a rank-two stored orthonormal frame has finrank exactly two. -/
theorem finrank_codeSpan (F : CodeSpec.OrthonormalFrame n 2) :
    Module.finrank ℂ (CodeSpec.codeSpan F) = 2 := by
  unfold CodeSpec.codeSpan
  simpa using finrank_span_eq_card (frame_linearIndependent F)

/-- For two rank-two orthonormal frames, containment of every vector of the
first in the second span already forces equality of code spans. -/
theorem codeSpan_eq_of_vec_mem
    (F G : CodeSpec.OrthonormalFrame n 2)
    (hmem : ∀ k, F.vec k ∈ CodeSpec.codeSpan G) :
    CodeSpec.codeSpan F = CodeSpec.codeSpan G := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.2
    rintro psi ⟨k, rfl⟩
    exact hmem k
  · rw [finrank_codeSpan, finrank_codeSpan]

end

end MainTheory.D3OrthonormalFrameSpan
