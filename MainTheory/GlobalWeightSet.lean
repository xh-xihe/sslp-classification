import MainTheory.OrderFiveEnumerator
import MainTheory.SixQubitIntrinsicAttainment
import MainTheory.WEStrictInclusion

/-!
# `eq:global-W-set` and the global conjecture it feeds

The manuscript defines

  `W^A_{6,2,3} := { (A_0(P), ..., A_6(P)) : P the projector of an exact
  ((6,2,3)) code }`,

the `A`-enumerator set of the whole code space with no transversal-gate
assumption, and then boxes a conjecture about it with `?=`.

No Lean definition formed that set.  Its ingredients were all present --
`CodeSpec.ExactCode 6 2 3` is the display's notion of code and
`CodeSpec.AWeight` is the paper's normalization `A_w = Aco_w / K^2` -- but
`Levels.WImage` is indexed by an angle vector and its two residues, so it is
the enumerator set of one *orbit*, never of the whole space.

`globalWSet` is the set itself.  It is recorded here with a nonvacuity witness
rather than left as a bare definition: the orbit-36 enumerator belongs to it,
because an exact code of intrinsic order five exists and every such code
carries that enumerator.

The conjecture is recorded as a proposition, not proved.  The manuscript marks
it `?=`; `WEStrictInclusion.conjecturedImages` is already the right-hand side,
and `GlobalWEConjecture` is the equality itself so that the display can be
cited without being asserted.
-/

namespace MainTheory.GlobalWeightSet

open MainTheory

/-- **`eq:global-W-set`.**  The `A`-enumerator set of the full `((6,2,3))`
code space. -/
def globalWSet : Set (Fin 7 → ℝ) :=
  { A | ∃ C : CodeSpec.ExactCode 6 2 3, ∀ j : Fin 7, A j = CodeSpec.AWeight C.frame (j : ℕ) }

/-- At one logical qubit the paper's normalization is `Aco / 4`. -/
theorem aweight_eq (F : CodeSpec.OrthonormalFrame 6 2) (w : ℕ) :
    CodeSpec.AWeight F w = SS.MacWilliams.Aco F.vec w / 4 := by
  norm_num [CodeSpec.AWeight]

/-- **The set is not vacuous.**  The orbit-36 enumerator lies in it: an exact
`((6,2,3))` code with an intrinsic element of order five exists, and every
such code carries that enumerator. -/
theorem R5A_mem_globalWSet : MainTheory.WImages.R5A ∈ globalWSet := by
  obtain ⟨C, g, _, hg5⟩ := MainTheory.SixQubitIntrinsicAttainment.order_five_attained
  refine ⟨C, fun j => ?_⟩
  rw [aweight_eq]
  exact (MainTheory.OrderFiveEnumerator.orderFive_enumerator C g hg5 j).symm

theorem globalWSet_nonempty : globalWSet.Nonempty :=
  ⟨MainTheory.WImages.R5A, R5A_mem_globalWSet⟩

/-- **`eq:global-WE-conjecture`**, as a proposition.

The manuscript boxes this with `?=` and does not assert it.  Recording it as a
`Prop` lets the display be cited without being claimed; nothing in this
repository proves it, and `WEStrictInclusion.provedImages_subset_conjectured`
gives only the inclusion of the eleven proved orbit images in the right-hand
side. -/
def GlobalWEConjecture : Prop :=
  globalWSet = MainTheory.WEStrictInclusion.conjecturedImages

end MainTheory.GlobalWeightSet
