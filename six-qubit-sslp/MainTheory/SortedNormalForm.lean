import MainTheory.RankTwoSSLP
import MainTheory.PermutationSemanticTransport

/-!
# The sorted canonical form `0 <= a_1 <= ... <= a_n < q`

`thm:rank-two-sslp` states its normal form with the angle vector sorted.  The
repository had the transport that makes sorting legitimate --
`PermutationSemanticTransport` moves angles, fibres, distance three and codes
through a qubit permutation -- but it was never composed with an actual sort:
`permFiniteGeneratorResolution` had no call site, and no theorem anywhere said
the angle could be taken monotone.

`SortedNormalForm` is the paper's normal form as a record, and
`exists_sortedNormalForm` builds one for every exact `((n,2,3))` code with a
projectively nontrivial diagonal symmetry.  The sort is `Tuple.sort` applied
to the residue representatives, and the qubit permutation is its inverse, so
that `PermutationSemanticTransport.permAngle` composes to the sorted vector.

The equivalence to `C` is recorded explicitly rather than left as "up to":
`source_span` says the source frame spans `C`'s code space, and `frame_eq`
says the normal-form frame is that source conjugated by the local `X` string
`x0` and permuted by `perm`.
-/

namespace MainTheory.SortedForm

open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SectionTwoGeneral
open MainTheory.D3NormalizedFreshPhase
open MainTheory.SixQubitSemanticEntrance
open MainTheory.PermutationSemanticTransport

variable {n : ℕ}

/-- **The rank-two normal form with a sorted angle vector.** -/
structure SortedNormalForm (C : CodeSpec.ExactCode n 2 3) where
  /-- The physical order. -/
  q : ℕ
  q_ne : NeZero q
  two_le_q : 2 ≤ q
  /-- The projective logical order. -/
  m : ℕ
  two_le_m : 2 ≤ m
  m_dvd_q : m ∣ q
  zeta : ℂ
  primitiveRoot : IsPrimitiveRoot zeta q
  /-- The angle vector, sorted. -/
  angle : Fin n → ZMod q
  sorted : Monotone fun j => (angle j).val
  lt_q : ∀ j, (angle j).val < q
  /-- The two logical states: an orthonormal pair with distance three. -/
  frame : CodeSpec.OrthonormalFrame n 2
  hasDistance : SS.HasDistance frame.vec 3
  /-- The two residue fibres, at `0` and `q/m`. -/
  leftFiber : SS.SSConditionState angle 0 (frame.vec 0)
  rightFiber : SS.SSConditionState angle (((q / m : ℕ) : ZMod q)) (frame.vec 1)
  /-- The explicit equivalence to `C`: a local `X` string and a permutation. -/
  x0 : SS.BitString n
  perm : Equiv.Perm (Fin n)
  source : CodeSpec.OrthonormalFrame n 2
  source_span : CodeSpec.codeSpan C.frame = CodeSpec.codeSpan source
  frame_eq : ∀ k s, frame.vec k s =
    source.vec k (SS.bxor (SixQubit.CodeEquiv.permStr perm s) x0)

attribute [instance] SortedNormalForm.q_ne

/-- The permutation that sorts a `ZMod q` vector by its residue
representative, in the convention `permAngle` uses. -/
def sortingPerm {q : ℕ} (a : Fin n → ZMod q) : Equiv.Perm (Fin n) :=
  (Tuple.sort fun j => (a j).val).symm

theorem monotone_permAngle_sortingPerm {q : ℕ} (a : Fin n → ZMod q) :
    Monotone fun j => ((permAngle (sortingPerm a) a) j).val := by
  have h := Tuple.monotone_sort fun j => (a j).val
  simpa [permAngle, sortingPerm, Function.comp] using h

/-- **Every exact rank-two distance-three code with a projectively nontrivial
diagonal symmetry has the sorted normal form.** -/
theorem exists_sortedNormalForm (C : CodeSpec.ExactCode n 2 3)
    (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    Nonempty (SortedNormalForm C) := by
  letI : NeZero (rationalLift C GeneralFiniteness.two_le_three theta hpres).order :=
    ⟨(rationalLift C GeneralFiniteness.two_le_three theta hpres).order_pos.ne'⟩
  set q := (rationalLift C GeneralFiniteness.two_le_three theta hpres).order with hq
  set G := finiteGenerator C GeneralFiniteness.two_le_three theta hpres hnt with hG
  set T := canonicalTwoFiber G with hT
  have hL : SS.SSConditionState (normalizedFiniteAngle G T) 0
      (normalizedState T 0) := T.normalizedLeft
  have hR : SS.SSConditionState (normalizedFiniteAngle G T)
      (((q / T.logicalOrder : ℕ) : ZMod q)) (normalizedState T 1) :=
    T.normalizedRight
  refine ⟨{
    q := q
    q_ne := inferInstance
    two_le_q := T.two_le_physicalOrder
    m := T.logicalOrder
    two_le_m := T.two_le_logicalOrder
    m_dvd_q := T.logicalOrder_dvd_physical
    zeta := G.zeta
    primitiveRoot := G.primitiveRoot
    angle := permAngle (sortingPerm (normalizedFiniteAngle G T))
      (normalizedFiniteAngle G T)
    sorted := monotone_permAngle_sortingPerm _
    lt_q := fun j => ZMod.val_lt _
    frame := PermutationFrameBridge.permFrame (normalizedFrame T)
      (sortingPerm (normalizedFiniteAngle G T))
    hasDistance := hasDistance_permAct _ (normalizedFrame T).vec
      (normalizedCode T).hasDistance
    leftFiber := ssConditionState_permAct _ _ 0 _ hL
    rightFiber := ssConditionState_permAct _ _ _ _ hR
    x0 := T.x0
    perm := sortingPerm (normalizedFiniteAngle G T)
    source := G.eigenFrame
    source_span := G.span_eq
    frame_eq := fun k s => rfl }⟩

end MainTheory.SortedForm
