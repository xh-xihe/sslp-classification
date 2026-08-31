import MainTheory.D3LogicalNormalization
import MainTheory.D3OrthonormalFrameSpan

/-!
# The normalized physical logical frame

The normalized coordinate vector and its normalized explicit perpendicular
are synthesized in the stored physical code frame.  Their exact coordinate
orthonormality is transported to `SS.innerC`, producing a genuine repository
`OrthonormalFrame`.  A finrank argument then proves that its code span is
exactly the original code span.
-/

namespace MainTheory.D3LogicalNormalizedFrame

open MainTheory
open MainTheory.D3LogicalCoordinateUnitary
open MainTheory.D3LogicalNormalization

noncomputable section

/-- The physical frame synthesized from a nonzero coordinate vector and its
explicit perpendicular. -/
def normalizedPhysicalFrame
    (F : CodeSpec.OrthonormalFrame 6 2) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    CodeSpec.OrthonormalFrame 6 2 where
  vec := ![
    D3LogicalAction.synthesisLinear F (normalized v),
    D3LogicalAction.synthesisLinear F (normalized (perpendicular v))]
  orthonormal := by
    intro i j
    fin_cases i <;> fin_cases j
    · change SS.innerC
          (D3LogicalAction.synthesisLinear F (normalized v))
          (D3LogicalAction.synthesisLinear F (normalized v)) = 1
      rw [D3LogicalCoordinateUnitary.innerC_synthesis,
        coordinateInner_normalized_self hv]
    · change SS.innerC
          (D3LogicalAction.synthesisLinear F (normalized v))
          (D3LogicalAction.synthesisLinear F
            (normalized (perpendicular v))) = 0
      rw [D3LogicalCoordinateUnitary.innerC_synthesis,
        coordinateInner_normalized_perpendicular]
    · change SS.innerC
          (D3LogicalAction.synthesisLinear F
            (normalized (perpendicular v)))
          (D3LogicalAction.synthesisLinear F (normalized v)) = 0
      rw [D3LogicalCoordinateUnitary.innerC_synthesis,
        coordinateInner_normalized_perpendicular_rev]
    · change SS.innerC
          (D3LogicalAction.synthesisLinear F
            (normalized (perpendicular v)))
          (D3LogicalAction.synthesisLinear F
            (normalized (perpendicular v))) = 1
      rw [D3LogicalCoordinateUnitary.innerC_synthesis,
        coordinateInner_normalized_self (perpendicular_ne_zero hv)]

/-- Every vector of the new physical frame belongs to the original code
span, because it is obtained by synthesis in the original frame. -/
theorem normalizedPhysicalFrame_vec_mem
    (F : CodeSpec.OrthonormalFrame 6 2) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (k : Fin 2) :
    (normalizedPhysicalFrame F v hv).vec k ∈ CodeSpec.codeSpan F := by
  fin_cases k
  · change D3LogicalAction.synthesisLinear F (normalized v) ∈
      CodeSpec.codeSpan F
    exact D3LogicalAction.synthesis_mem_codeSpan F (normalized v)
  · change D3LogicalAction.synthesisLinear F
        (normalized (perpendicular v)) ∈ CodeSpec.codeSpan F
    exact D3LogicalAction.synthesis_mem_codeSpan F
      (normalized (perpendicular v))

/-- The new normalized frame spans exactly the original physical code. -/
theorem codeSpan_normalizedPhysicalFrame
    (F : CodeSpec.OrthonormalFrame 6 2) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    CodeSpec.codeSpan F =
      CodeSpec.codeSpan (normalizedPhysicalFrame F v hv) := by
  symm
  exact D3OrthonormalFrameSpan.codeSpan_eq_of_vec_mem
    (normalizedPhysicalFrame F v hv) F
    (normalizedPhysicalFrame_vec_mem F v hv)

end

end MainTheory.D3LogicalNormalizedFrame
