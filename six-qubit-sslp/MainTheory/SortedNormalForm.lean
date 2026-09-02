import MainTheory.RankTwoSSLP
import MainTheory.PermutationSemanticTransport
import MainTheory.D3BoundedOuterRecord

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
structure SortedNormalForm {d : ℕ} (C : CodeSpec.ExactCode n 2 d) where
  /-- The physical order. -/
  q : ℕ
  q_ne : NeZero q
  two_le_q : 2 ≤ q
  /-- The projective logical order. -/
  m : ℕ
  two_le_m : 2 ≤ m
  m_dvd_q : m ∣ q
  /-- `m` really is a projective logical order: it is the order of an actual
  element of the intrinsic group, not merely a divisor of `q` that happens to
  fit the fibre condition.  Without this the field's name would be an
  assertion the record does not make. -/
  m_isOrder : ∃ g : GlobalClassificationBridge.IntrinsicGroup C,
    orderOf g = m
  zeta : ℂ
  primitiveRoot : IsPrimitiveRoot zeta q
  /-- The angle vector: `0 <= a_1 <= ... <= a_n < q` with
  `gcd(q, a_1, ..., a_n) = 1`, which is the paper's `eq:a-canonical`. -/
  angle : Fin n → ZMod q
  sorted : Monotone fun j => (angle j).val
  lt_q : ∀ j, (angle j).val < q
  primitive : Gate.Primitive q angle
  /-- The two logical states: an orthonormal pair with distance three. -/
  frame : CodeSpec.OrthonormalFrame n 2
  hasDistance : SS.HasDistance frame.vec d
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

/-! ## The record's operator content

The two fibre conditions are stated on subset-sum residues, which is what the
enumeration consumes.  They are equivalent to the operator statement the paper
writes -- `D(a;q)` acts diagonally on the two logical words with eigenvalues
`1` and `omega_q^{q/m}` -- and that equivalence is `PhaseSector`.  Recording it
here keeps `zeta` from being an inert field: the record really does say the
gate acts. -/

/-- **`D(a;q)` fixes the first logical word.** -/
theorem SortedNormalForm.gate_left {d : ℕ} {C : CodeSpec.ExactCode n 2 d}
    (S : SortedNormalForm C) :
    Gate.gate S.zeta S.angle (S.frame.vec 0) = S.frame.vec 0 := by
  have h := MainTheory.PhaseSector.eigen_of_ssCondition S.zeta S.angle (S.frame.vec 0) 0
    S.leftFiber
  simpa using h

/-- **`q` is the exact physical order of `D(a;q)`**, not merely an exponent
that kills it.  This is what the record's primitivity clause buys, and it is
the sense in which `eq:primitive` makes `q` an invariant. -/
theorem SortedNormalForm.physicalOrder {d : ℕ} {C : CodeSpec.ExactCode n 2 d}
    (S : SortedNormalForm C) (k : ℕ) :
    (∀ s : SS.BitString n, Gate.diag S.zeta S.angle s ^ k = 1) ↔ S.q ∣ k :=
  Gate.pow_eq_one_iff S.zeta S.primitiveRoot S.angle S.primitive k

/-- **`m` is the exact projective logical order of the displayed gate.**

`m_isOrder` says `m` is the order of some group element; this says it is the
order of *this* gate's logical action, which is the paper's `C_m`. -/
theorem SortedNormalForm.projectiveOrder {d : ℕ}
    {C : CodeSpec.ExactCode n 2 d} (S : SortedNormalForm C) (k : ℕ) :
    Cyclic.chi S.zeta (((S.q / S.m : ℕ) : ZMod S.q)) ^ k = 1 ↔ S.m ∣ k := by
  haveI := S.q_ne
  rw [Cyclic.chi_pow_eq_one_iff S.zeta S.primitiveRoot,
    RankTwo.addOrderOf_div S.m S.m_dvd_q]

/-- The right residue does not wrap: its `ZMod q` representative is literally
`q / m`.  Without this the eigenvalue below could not be read as the paper's
`omega_q^{q/m}`. -/
theorem SortedNormalForm.val_rightResidue {d : ℕ}
    {C : CodeSpec.ExactCode n 2 d} (S : SortedNormalForm C) :
    (((S.q / S.m : ℕ) : ZMod S.q)).val = S.q / S.m := by
  haveI := S.q_ne
  refine ZMod.val_natCast_of_lt ?_
  have hq : 0 < S.q := by have := S.two_le_q; omega
  have hm : 1 < S.m := by have := S.two_le_m; omega
  exact Nat.div_lt_self hq hm

/-- **`D(a;q)` scales the second logical word by `omega_q^{q/m}`.** -/
theorem SortedNormalForm.gate_right {d : ℕ} {C : CodeSpec.ExactCode n 2 d}
    (S : SortedNormalForm C) :
    Gate.gate S.zeta S.angle (S.frame.vec 1)
      = fun s => S.zeta ^ (S.q / S.m) * S.frame.vec 1 s := by
  rw [← S.val_rightResidue]
  exact MainTheory.PhaseSector.eigen_of_ssCondition S.zeta S.angle
    (S.frame.vec 1) _ S.rightFiber

/-- The permutation that sorts a `ZMod q` vector by its residue
representative, in the convention `permAngle` uses. -/
def sortingPerm {q : ℕ} (a : Fin n → ZMod q) : Equiv.Perm (Fin n) :=
  (Tuple.sort fun j => (a j).val).symm

theorem monotone_permAngle_sortingPerm {q : ℕ} (a : Fin n → ZMod q) :
    Monotone fun j => ((permAngle (sortingPerm a) a) j).val := by
  have h := Tuple.monotone_sort fun j => (a j).val
  simpa [permAngle, sortingPerm, Function.comp] using h

/-- **Any finite generator resolution yields the sorted normal form**, of the
generator's own modulus.

Stated on an arbitrary resolution rather than on the one `finiteGenerator`
produces, so that a resolution carrying a bound can be fed in instead. -/
theorem exists_sortedNormalForm_of_generator {d q : ℕ} [NeZero q]
    (C : CodeSpec.ExactCode n 2 d)
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    ∃ S : SortedNormalForm C, S.q = q := by
  set T := canonicalTwoFiber G with hT
  have hL : SS.SSConditionState (normalizedFiniteAngle G T) 0
      (normalizedState (d := d) T 0) := T.normalizedLeft
  have hR : SS.SSConditionState (normalizedFiniteAngle G T)
      (((q / T.logicalOrder : ℕ) : ZMod q))
      (normalizedState (d := d) T 1) :=
    T.normalizedRight
  refine ⟨{
    q := q
    q_ne := inferInstance
    two_le_q := T.two_le_physicalOrder
    m := T.logicalOrder
    two_le_m := T.two_le_logicalOrder
    m_dvd_q := T.logicalOrder_dvd_physical
    m_isOrder := ⟨G.intrinsicClass, T.intrinsic_order_eq⟩
    zeta := G.zeta
    primitiveRoot := G.primitiveRoot
    angle := permAngle (sortingPerm (normalizedFiniteAngle G T))
      (normalizedFiniteAngle G T)
    sorted := monotone_permAngle_sortingPerm _
    primitive := primitive_permAngle _ _
      (D3BoundedOuterRecord.primitive_unit_mul T.unit
        (Normalize.flip G.angle T.x0)
        (Normalize.primitive_flip G.angle T.x0 G.primitive))
    lt_q := fun j => ZMod.val_lt _
    frame := PermutationFrameBridge.permFrame (normalizedFrame T)
      (sortingPerm (normalizedFiniteAngle G T))
    hasDistance := hasDistance_permAct _ (normalizedFrame T).vec
      T.normalizedHasDistance
    leftFiber := ssConditionState_permAct _ _ 0 _ hL
    rightFiber := ssConditionState_permAct _ _ _ _ hR
    x0 := T.x0
    perm := sortingPerm (normalizedFiniteAngle G T)
    source := G.eigenFrame
    source_span := G.span_eq
    frame_eq := fun k s => rfl }, rfl⟩

/-- **The same, remembering where the frame came from.**

`exists_sortedNormalForm_of_generator` throws away the relation between the
normal form and the generator it was built from, and with it the fact --
`RankTwoGlobal.TwoFiberCertificate.base_supported` -- that the normalization
shift is by a point of the first logical word's own support.  Downstream that
fact is what makes the *zero* word lie in the normalized support, where a
support's affine and linear ranks agree.  This variant keeps both.

It is stated separately rather than by strengthening the original, so that no
existing destructuring breaks. -/
theorem exists_sortedNormalForm_of_generator' {d q : ℕ} [NeZero q]
    (C : CodeSpec.ExactCode n 2 d)
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    ∃ S : SortedNormalForm C,
      S.q = q ∧ S.source = G.eigenFrame ∧ G.eigenFrame.vec 0 S.x0 ≠ 0 := by
  set T := canonicalTwoFiber G with hT
  have hL : SS.SSConditionState (normalizedFiniteAngle G T) 0
      (normalizedState (d := d) T 0) := T.normalizedLeft
  have hR : SS.SSConditionState (normalizedFiniteAngle G T)
      (((q / T.logicalOrder : ℕ) : ZMod q))
      (normalizedState (d := d) T 1) :=
    T.normalizedRight
  refine ⟨{
    q := q
    q_ne := inferInstance
    two_le_q := T.two_le_physicalOrder
    m := T.logicalOrder
    two_le_m := T.two_le_logicalOrder
    m_dvd_q := T.logicalOrder_dvd_physical
    m_isOrder := ⟨G.intrinsicClass, T.intrinsic_order_eq⟩
    zeta := G.zeta
    primitiveRoot := G.primitiveRoot
    angle := permAngle (sortingPerm (normalizedFiniteAngle G T))
      (normalizedFiniteAngle G T)
    sorted := monotone_permAngle_sortingPerm _
    primitive := primitive_permAngle _ _
      (D3BoundedOuterRecord.primitive_unit_mul T.unit
        (Normalize.flip G.angle T.x0)
        (Normalize.primitive_flip G.angle T.x0 G.primitive))
    lt_q := fun j => ZMod.val_lt _
    frame := PermutationFrameBridge.permFrame (normalizedFrame T)
      (sortingPerm (normalizedFiniteAngle G T))
    hasDistance := hasDistance_permAct _ (normalizedFrame T).vec
      T.normalizedHasDistance
    leftFiber := ssConditionState_permAct _ _ 0 _ hL
    rightFiber := ssConditionState_permAct _ _ _ _ hR
    x0 := T.x0
    perm := sortingPerm (normalizedFiniteAngle G T)
    source := G.eigenFrame
    source_span := G.span_eq
    frame_eq := fun k s => rfl }, rfl, rfl, T.base_supported⟩

/-- **Every exact rank-two code of distance at least two with a projectively
nontrivial diagonal symmetry has the sorted normal form.** -/
theorem exists_sortedNormalForm {d : ℕ} (hd : 2 ≤ d)
    (C : CodeSpec.ExactCode n 2 d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C,
      S.q = (rationalLift C hd theta hpres).order := by
  letI : NeZero (rationalLift C hd theta hpres).order :=
    ⟨(rationalLift C hd theta hpres).order_pos.ne'⟩
  exact exists_sortedNormalForm_of_generator C
    (finiteGenerator C hd theta hpres hnt)

/-- The `Nonempty` form, for callers that do not need the modulus named. -/
theorem nonempty_sortedNormalForm {d : ℕ} (hd : 2 ≤ d)
    (C : CodeSpec.ExactCode n 2 d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    Nonempty (SortedNormalForm C) :=
  let ⟨S, _⟩ := exists_sortedNormalForm hd C theta hpres hnt
  ⟨S⟩

/-- **The normal form's modulus obeys `beta_{n+1}`.**

At rank two a projectively nontrivial operation has exactly two logical
eigenvalues, so the coloured system has `n + 1` unknowns; and `rationalLift` is
the pivot lift, so its modulus is bounded. -/
theorem exists_sortedNormalForm_le {B d : ℕ} (hd : 2 ≤ d)
    (beta : BinaryBeta.BetaBound (n + 1) B)
    (C : CodeSpec.ExactCode n 2 d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C, S.q ≤ B := by
  obtain ⟨S, hSq⟩ := exists_sortedNormalForm hd C theta hpres hnt
  refine ⟨S, ?_⟩
  rw [hSq]
  have ht : 2 ≤ (resolutionOf C theta hpres).sectorCount :=
    two_le_sectorCount_of_projectively_nontrivial C theta hpres hnt
  have h2 : (resolutionOf C theta hpres).sectorCount = 2 :=
    sectorCount_eq_two C theta hpres hnt
  refine rationalLift_order_le C hd theta hpres ?_ ht
  rw [h2]
  simpa using beta

/-- **`thm:d2-sslp-classification`.**

Fix `n` and a target distance `d0 >= 2`.  Every exact `((n,2,d))` code with
`d >= d0` carrying a projectively nontrivial diagonal operation occurs in a
primitive sector with

  `2 <= q <= beta_{n+1}`, `m | q`, `m >= 2`,
  `0 <= a_1 <= ... <= a_n < q`, `gcd(q, a_1, ..., a_n) = 1`,

with the two logical words supported in the fibres `0` and `q/m` of that
sector, orthonormal, and satisfying the Knill--Laflamme equations for every
Pauli of weight below `d` -- hence below `d0`.

All of that is the record `SortedNormalForm`; what this theorem adds is the
bound, and the fact that the record exists at every `d >= d0`. -/
theorem d2_sslp_classification {B d0 d : ℕ} (hd0 : 2 ≤ d0) (hdd : d0 ≤ d)
    (beta : BinaryBeta.BetaBound (n + 1) B)
    (C : CodeSpec.ExactCode n 2 d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C, S.q ≤ B ∧ 2 ≤ S.q ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      Monotone (fun j => (S.angle j).val) ∧
      Gate.Primitive S.q S.angle ∧
      SS.HasDistance S.frame.vec d := by
  obtain ⟨S, hSB⟩ :=
    exists_sortedNormalForm_le (le_trans hd0 hdd) beta C theta hpres hnt
  exact ⟨S, hSB, S.two_le_q, S.two_le_m, S.m_dvd_q, S.sorted, S.primitive,
    S.hasDistance⟩

end MainTheory.SortedForm

