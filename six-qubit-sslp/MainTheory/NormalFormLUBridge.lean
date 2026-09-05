import MainTheory.SpanProjectorBridge
import MainTheory.SortedNormalForm
import MainTheory.LocalMonomialSixBridge

/-!
# The sorted normal form is a local-unitary move on the code

`SortedForm.SortedNormalForm` records its relation to the code it was built
from in two fields, and neither was ever cashed out at the level of
projectors.  `source_span` says the source frame spans the code space;
`frame_eq` says the record's own frame is that source conjugated by a local
`X` string and permuted.  `SSLPCompleteness.hasDistance_normalForm` performs
the same decomposition, but only to move the Knill--Laflamme predicate; it
produces no equivalence and no LU statement.

Both halves are local-unitary facts and this file says so:

* `equivalent_source_frame` -- `frame_eq` *is* a `CodeEquiv.Equivalent`, with
  the local monomial carrying unit phases, permutation `S.perm` and flip
  `permStr S.perm.symm S.x0`.  The inverse permutation on the flip is forced:
  `frame_eq` permutes and then flips, while `LocalMonomial.act` flips and then
  permutes.
* `ofFrame_eq_of_codeSpan_eq` from `SpanProjectorBridge` turns `source_span`
  into an equality of projectors.

Composing them, `luEquivalent_ofFrame_normalForm` says the code's own projector
is local-unitarily equivalent to the normal form's.  That is the step which
lets a theorem proved about a normal form -- everything the six-qubit directory
knows -- be read back as a theorem about the code.
-/

namespace MainTheory.NormalFormLUBridge

open MainTheory
open MainTheory.CodeSpec
open MainTheory.ClassificationLevels
open MainTheory.SortedForm

variable {n d : ℕ}

/-- **The normal form's frame is a code equivalence of its source.**

`S.frame_eq` reads `frame.vec k s = source.vec k (bxor (permStr S.perm s) S.x0)`.
`LocalMonomial.act` reads `U.act psi s = (phases) * psi (permStr U.perm (bxor s U.flip))`.
Matching them needs `permStr S.perm (bxor s U.flip) = bxor (permStr S.perm s) S.x0`,
which `permStr_bxor` reduces to `permStr S.perm U.flip = S.x0`; hence the flip
is `permStr S.perm.symm S.x0`, not `S.x0`. -/
theorem equivalent_source_frame {C : CodeSpec.ExactCode n 2 d}
    (S : SortedNormalForm C) :
    SixQubit.CodeEquiv.Equivalent S.source.vec S.frame.vec := by
  refine ⟨⟨S.perm, SixQubit.CodeEquiv.permStr S.perm.symm S.x0,
    fun _ => 1, fun _ => 1, fun _ => by simp, fun _ => by simp⟩,
    fun _ => 1, false, fun _ => by simp, ?_⟩
  intro k
  funext s
  have hflip : SixQubit.CodeEquiv.permStr S.perm
      (SixQubit.CodeEquiv.permStr S.perm.symm S.x0) = S.x0 := by
    funext i
    simp [SixQubit.CodeEquiv.permStr]
  simp only [SixQubit.CodeEquiv.scal,
    SixQubit.CodeEquiv.LocalMonomial.act_apply,
    SixQubit.CodeEquiv.permStr_bxor, hflip]
  simp [S.frame_eq k s, SixQubit.CodeEquiv.swapIdx]

/-- **The code and its normal form have the same projector, up to a local
unitary.**

The span half is an equality of projectors, not merely an equivalence; the
frame half is a genuine local-unitary move.  Together they carry any
projector-level statement about the normal form back to the code. -/
theorem luEquivalent_ofFrame_normalForm {C : CodeSpec.ExactCode 6 2 d}
    (S : SortedNormalForm C) :
    LUEquivalent (CodeProjector.ofFrame C.frame)
      (CodeProjector.ofFrame S.frame) := by
  have hspan : CodeProjector.ofFrame C.frame = CodeProjector.ofFrame S.source :=
    MainTheory.SpanProjectorBridge.ofFrame_eq_of_codeSpan_eq _ _ S.source_span
  rw [hspan]
  exact MainTheory.LocalMonomialSixBridge.luEquivalent_of_codeEquivalent
    S.source S.frame (equivalent_source_frame S)

end MainTheory.NormalFormLUBridge
