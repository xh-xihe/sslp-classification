import MainTheory.ClassificationLevels

/-!
# Equal code spans give the same projector

`SortedForm.SortedNormalForm` relates its own frame to the code it came from
by `source_span`, an equality of *code spans*, and by `frame_eq`, an explicit
local `X` string and qubit permutation.  The second is already a code
equivalence in the paper's sense; the first was a dead end, because nothing
anywhere turned an equality of spans into a statement about projectors.  Every
span-transport lemma in the tree carried the Knill--Laflamme predicate
(`hasDistance_of_codeSpan_eq`) and stopped there.

That is the one piece with mathematical content in carrying `thm:unique-C5-LU`
from codes already supported on orbit 36's table fibres to an arbitrary
order-five code, and it is the standard fact that two orthogonal projections
with the same range coincide.  The proof here is the standard one, in the
repository's own bra--ket vocabulary:

* `innerC_projectorAction_of_mem` -- projecting does not change the inner
  product against *any* vector of the span, not merely against a frame vector.
  This is `CodeSpec.innerC_projectorAction` extended by span induction.
* `projectorAction_eq_of_codeSpan_eq` -- hence each projector fixes the other's
  output and reproduces the other's coefficients, so the two actions agree.
* `ofFrame_eq_of_codeSpan_eq` -- reading the actions at the delta states turns
  that into equality of kernels, and `CodeProjector.ext` finishes.

Note the ranks are allowed to differ: nothing here needs `K = L`, since equal
spans already force equal dimensions.
-/

namespace MainTheory.SpanProjectorBridge

open MainTheory.CodeSpec
open MainTheory.ClassificationLevels

variable {n K L : ℕ}

/-- **Projection is invisible to the whole span, not just to the frame.**

`innerC_projectorAction` says the projector does not change the inner product
against a frame vector; span induction extends that to every vector of the
code span.  Conjugate linearity in the left slot is exactly what
`innerC_add_left` and `innerC_smul_left` supply. -/
theorem innerC_projectorAction_of_mem (F : OrthonormalFrame n K)
    (phi : SS.State n ℂ) {v : SS.State n ℂ} (hv : v ∈ codeSpan F) :
    SS.innerC v (projectorAction F phi) = SS.innerC v phi := by
  refine Submodule.span_induction
    (p := fun v _ => SS.innerC v (projectorAction F phi) = SS.innerC v phi)
    ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨j, rfl⟩
    exact innerC_projectorAction F j phi
  · simp
  · intro x y _ _ hx hy
    rw [innerC_add_left, innerC_add_left, hx, hy]
  · intro a x _ hx
    rw [innerC_smul_left, innerC_smul_left, hx]

/-- **Two frames with the same span have the same projector action.**

`projectorAction F phi` lies in `codeSpan F = codeSpan G`, so `G`'s projector
fixes it; and `G`'s coefficients cannot tell `phi` from `projectorAction F phi`,
by the previous lemma applied to `G.vec k`, which lies in `codeSpan F`. -/
theorem projectorAction_eq_of_codeSpan_eq (F : OrthonormalFrame n K)
    (G : OrthonormalFrame n L) (h : codeSpan F = codeSpan G)
    (phi : SS.State n ℂ) :
    projectorAction F phi = projectorAction G phi := by
  have hfix : projectorAction G (projectorAction F phi) = projectorAction F phi := by
    rw [← mem_codeSpan_iff_projectorAction_eq, ← h]
    exact projectorAction_mem_codeSpan F phi
  have hcoeff : projectorAction G (projectorAction F phi)
      = projectorAction G phi := by
    funext x
    simp only [projectorAction]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hmem : G.vec k ∈ codeSpan F := by
      rw [h]
      exact Submodule.subset_span (Set.mem_range_self k)
    rw [innerC_projectorAction_of_mem F phi hmem]
  rw [← hfix, hcoeff]

/-- The same, at the level of kernels. -/
theorem projectorKernel_eq_of_codeSpan_eq (F : OrthonormalFrame n K)
    (G : OrthonormalFrame n L) (h : codeSpan F = codeSpan G) :
    projectorKernel F = projectorKernel G := by
  classical
  funext x y
  have hact := congrFun
    (projectorAction_eq_of_codeSpan_eq F G h (fun z => if z = y then (1 : ℂ) else 0)) x
  rw [projectorAction_eq_kernel, projectorAction_eq_kernel] at hact
  simpa using hact

/-- **Equal code spans give the same code projector.**

This is what `SortedNormalForm.source_span` is worth: the normal form's source
frame and the code's own frame are not merely spanning the same space, they
define the same projector, so any statement about one is a statement about the
other. -/
theorem ofFrame_eq_of_codeSpan_eq (F : OrthonormalFrame n K)
    (G : OrthonormalFrame n L) (h : codeSpan F = codeSpan G) :
    CodeProjector.ofFrame F = CodeProjector.ofFrame G :=
  CodeProjector.ext (projectorKernel_eq_of_codeSpan_eq F G h)

end MainTheory.SpanProjectorBridge
