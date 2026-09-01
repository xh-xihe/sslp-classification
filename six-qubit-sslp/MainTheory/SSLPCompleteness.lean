import MainTheory.D3BoundedNormalForm

/-!
# `thm:sslp-completeness`: nothing escapes the finite outer enumeration

The theorem fixes a target distance `d0 >= 2`, defines the cutoff

  `B_{n,d0} = beta_{n+1}` for `d0 = 2`,  `beta_n` for `d0 >= 3`   (`eq:Bnd0`),

enumerates every primitive triple `2 <= q <= B_{n,d0}`, `m | q`, `m > 1`,
`0 <= a_1 <= ... <= a_n < q`, `gcd(q, a) = 1`, and then decides the
Knill--Laflamme system on each.  Its content splits in two.  The algorithmic
half -- that solving the equations exactly produces neither false positives nor
false negatives, and that the group audit and equivalence quotient return the
selected data -- is a statement about a procedure.  The mathematical half is
that *no code is missed*: every code in the class occurs in the enumeration.
That half is what is proved here, and it is exactly
`thm:d2-sslp-classification` and `thm:d3-sslp-classification` read as a
covering statement.

The two cases are separate theorems rather than one, because the record they
produce lives over a code of the corresponding distance, and a single statement
would have a type that changes with the branch.

A code of distance `d` is a code of every smaller distance -- detection is
antitone in the Pauli weight -- so the `d0 >= 3` case applies to every `d >= d0`
by viewing the code at distance three.  Its own Knill--Laflamme system at weight
below `d` is untouched and remains `C.hasDistance`; the enumeration checks it
separately, which is what the paper's "decide the complete Knill--Laflamme
polynomial system" step does.
-/

namespace MainTheory.SSLPCompleteness

open MainTheory
open MainTheory.SectionTwoGeneral

noncomputable section

variable {n : ℕ}

/-- **A code of distance `d` is a code of every smaller distance.**

`SS.HasDistance p d` is `SS.Detects p (d - 1)`, and `Detects` is antitone in
the weight. -/
def weakenDistance {d d0 : ℕ} (h : d0 ≤ d) (C : CodeSpec.ExactCode n 2 d) :
    CodeSpec.ExactCode n 2 d0 where
  positiveRank := C.positiveRank
  frame := C.frame
  hasDistance := by
    intro P hP
    exact C.hasDistance P (le_trans hP (Nat.sub_le_sub_right h 1))

@[simp] theorem weakenDistance_frame {d d0 : ℕ} (h : d0 ≤ d)
    (C : CodeSpec.ExactCode n 2 d) :
    (weakenDistance h C).frame = C.frame := rfl

/-- **The normal form inherits the original code's distance.**

The record built over the distance-three weakening only records distance three,
but the pair it displays is the original code's frame moved by a local `X`
string and a permutation, and both preserve the Knill--Laflamme system.  So the
enumeration's candidate really does satisfy the equations for every Pauli of
weight below `d`, which is what `thm:sslp-completeness` asks at target distance
`d0 <= d`. -/
theorem hasDistance_normalForm {d0 d : ℕ} (h : d0 ≤ d)
    (C : CodeSpec.ExactCode n 2 d)
    (S : SortedForm.SortedNormalForm (weakenDistance h C)) :
    SS.HasDistance S.frame.vec d := by
  have hsource : SS.HasDistance S.source.vec d :=
    CodeSpec.hasDistance_of_codeSpan_eq C.frame S.source S.source_span
      C.hasDistance
  have hflip : SS.HasDistance
      (fun k s => S.source.vec k (SS.bxor s S.x0)) d :=
    RankTwoGlobal.hasDistance_bxor S.source.vec S.x0 hsource
  have hperm := PermutationSemanticTransport.hasDistance_permAct S.perm
    (fun k s => S.source.vec k (SS.bxor s S.x0)) hflip
  have hEq : S.frame.vec
      = fun k => SixQubit.CodeEquiv.permAct S.perm
          (fun s => S.source.vec k (SS.bxor s S.x0)) := by
    funext k s
    exact S.frame_eq k s
  rw [hEq]
  exact hperm

/-- **`eq:Bnd0`**, the controlled outer cutoff. -/
def outerCutoff (B1 Bn d0 : ℕ) : ℕ := if d0 ≤ 2 then B1 else Bn

@[simp] theorem outerCutoff_two (B1 Bn : ℕ) : outerCutoff B1 Bn 2 = B1 := by
  simp [outerCutoff]

theorem outerCutoff_of_three_le (B1 Bn : ℕ) {d0 : ℕ} (h : 3 ≤ d0) :
    outerCutoff B1 Bn d0 = Bn := by
  simp [outerCutoff, Nat.not_le.2 (by omega : 2 < d0)]

/-- **Completeness at target distance two.**

Every exact `((n,2,d))` code with `d >= 2` carrying a projectively nontrivial
diagonal operation occurs in the enumeration at cutoff `beta_{n+1}`. -/
theorem completeness_distance_two {B1 Bn d0 d : ℕ} (hd0 : d0 = 2)
    (hdd : d0 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n + 1) B1)
    (C : CodeSpec.ExactCode n 2 d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedForm.SortedNormalForm C,
      2 ≤ S.q ∧ S.q ≤ outerCutoff B1 Bn d0 ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      (∃ g : GlobalClassificationBridge.IntrinsicGroup C, orderOf g = S.m) ∧
      Monotone (fun j => (S.angle j).val) ∧
      (∀ j, (S.angle j).val < S.q) ∧
      Gate.Primitive S.q S.angle ∧
      SS.HasDistance S.frame.vec d := by
  subst hd0
  obtain ⟨S, hSB⟩ :=
    SortedForm.exists_sortedNormalForm_le hdd beta1 C theta hpres hnt
  refine ⟨S, S.two_le_q, ?_, S.two_le_m, S.m_dvd_q, S.m_isOrder, S.sorted,
    S.lt_q, S.primitive, S.hasDistance⟩
  rw [outerCutoff_two]
  exact hSB

/-- **Completeness at target distance three or more.**

The same, at cutoff `beta_n`, for every `d >= d0 >= 3`.  The record is taken on
the code viewed at distance three, which is where the sparse binary simplex
lives; the code's own Knill--Laflamme system at weight below `d` is
`C.hasDistance` and is unaffected. -/
theorem completeness_distance_three {B1 Bn d0 d : ℕ} (hd0 : 3 ≤ d0)
    (hdd : d0 ≤ d)
    (betan : BinaryBeta.BetaBound n Bn)
    (C : CodeSpec.ExactCode n 2 d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedForm.SortedNormalForm
        (weakenDistance (show 3 ≤ d by omega) C),
      2 ≤ S.q ∧ S.q ≤ outerCutoff B1 Bn d0 ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      (∃ g : GlobalClassificationBridge.IntrinsicGroup
        (weakenDistance (show 3 ≤ d by omega) C), orderOf g = S.m) ∧
      Monotone (fun j => (S.angle j).val) ∧
      (∀ j, (S.angle j).val < S.q) ∧
      Gate.Primitive S.q S.angle ∧
      SS.HasDistance S.frame.vec d := by
  obtain ⟨S, hSB⟩ :=
    D3BoundedNormalForm.exists_sortedNormalForm_le_betaN betan
      (weakenDistance (show 3 ≤ d by omega) C) theta hpres hnt
  refine ⟨S, S.two_le_q, ?_, S.two_le_m, S.m_dvd_q, S.m_isOrder, S.sorted,
    S.lt_q, S.primitive, hasDistance_normalForm _ C S⟩
  rw [outerCutoff_of_three_le B1 Bn hd0]
  exact hSB

/-- **The six-qubit instance of the cutoff**, with no hypothesis: `beta_6 = 9`
is a kernel theorem, so at target distance three every six-qubit code in the
class occurs in the enumeration `2 <= q <= 9`. -/
theorem completeness_six_qubit {d0 d : ℕ} (hd0 : 3 ≤ d0) (hdd : d0 ≤ d)
    (C : CodeSpec.ExactCode 6 2 d) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedForm.SortedNormalForm
        (weakenDistance (show 3 ≤ d by omega) C),
      2 ≤ S.q ∧ S.q ≤ 9 ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      (∃ g : GlobalClassificationBridge.IntrinsicGroup
        (weakenDistance (show 3 ≤ d by omega) C), orderOf g = S.m) ∧
      Monotone (fun j => (S.angle j).val) ∧
      (∀ j, (S.angle j).val < S.q) ∧
      Gate.Primitive S.q S.angle ∧
      SS.HasDistance S.frame.vec d := by
  obtain ⟨S, h2q, hq, h2m, hmq, hord, hsort, hlt, hprim, hdist⟩ :=
    completeness_distance_three (B1 := 0) hd0 hdd
      MainTheory.Generated.BinaryBetaSixKernel.Certificate.upper C theta hpres
      hnt
  refine ⟨S, h2q, ?_, h2m, hmq, hord, hsort, hlt, hprim, hdist⟩
  rwa [outerCutoff_of_three_le 0 9 hd0] at hq

/-! ## The paper's own hypothesis

`thm:sslp-completeness` assumes the code "admits a nontrivial diagonal product
logical operation", which is a statement about the group.  The theorems above
take a real phase vector already known to act projectively nontrivially.  The
two are equivalent, and the translation is done here rather than left to the
reader. -/

/-- **Completeness at target distance two, under the paper's hypothesis.** -/
theorem completeness_of_nontrivial_two {B1 Bn d0 d : ℕ} (hd0 : d0 = 2)
    (hdd : d0 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n + 1) B1)
    (C : CodeSpec.ExactCode n 2 d)
    (hnontrivial : ∃ g : GlobalClassificationBridge.IntrinsicGroup C, g ≠ 1) :
    ∃ S : SortedForm.SortedNormalForm C,
      2 ≤ S.q ∧ S.q ≤ outerCutoff B1 Bn d0 ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      (∃ g : GlobalClassificationBridge.IntrinsicGroup C, orderOf g = S.m) ∧
      Monotone (fun j => (S.angle j).val) ∧
      (∀ j, (S.angle j).val < S.q) ∧
      Gate.Primitive S.q S.angle ∧
      SS.HasDistance S.frame.vec d := by
  obtain ⟨g, hg1⟩ := hnontrivial
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector
      (v : ClassificationLevels.LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (v : ClassificationLevels.LocalPhase n) v.2 theta hexp
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (v : ClassificationLevels.LocalPhase n) v.2 theta hexp hg1
  exact completeness_distance_two hd0 hdd beta1 C theta hpres hnt

/-- **Completeness at target distance three or more, under the paper's
hypothesis.** -/
theorem completeness_of_nontrivial_three {B1 Bn d0 d : ℕ} (hd0 : 3 ≤ d0)
    (hdd : d0 ≤ d)
    (betan : BinaryBeta.BetaBound n Bn)
    (C : CodeSpec.ExactCode n 2 d)
    (hnontrivial : ∃ g : GlobalClassificationBridge.IntrinsicGroup C, g ≠ 1) :
    ∃ S : SortedForm.SortedNormalForm
        (weakenDistance (show 3 ≤ d by omega) C),
      2 ≤ S.q ∧ S.q ≤ outerCutoff B1 Bn d0 ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      (∃ g : GlobalClassificationBridge.IntrinsicGroup
        (weakenDistance (show 3 ≤ d by omega) C), orderOf g = S.m) ∧
      Monotone (fun j => (S.angle j).val) ∧
      (∀ j, (S.angle j).val < S.q) ∧
      Gate.Primitive S.q S.angle ∧
      SS.HasDistance S.frame.vec d := by
  obtain ⟨g, hg1⟩ := hnontrivial
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector
      (v : ClassificationLevels.LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (v : ClassificationLevels.LocalPhase n) v.2 theta hexp
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (v : ClassificationLevels.LocalPhase n) v.2 theta hexp hg1
  exact completeness_distance_three hd0 hdd betan C theta hpres hnt

/-! ## `eq:m-leq9`: the six-qubit order bound -/

/-- **`eq:m-leq9`.**  Every projective diagonal logical element of an exact
`((6,2,3))` code has order at most nine.

Immediate from the unconditional six-qubit bounded representation: the class has
a representative gate of modulus `q' <= 9`, and that gate's `q'`-th power is the
identity, so the class's order divides `q'`. -/
theorem orderOf_le_nine (C : CodeSpec.ExactCode 6 2 3)
    (g : GlobalClassificationBridge.IntrinsicGroup C) : orderOf g ≤ 9 := by
  obtain ⟨lbl, u, hclass, hgate⟩ :=
    BoundedRepresentationCertified.hasBoundedRepresentation_unconditional C g
  have hpow : u ^ (lbl.1.val + 1) = 1 := by
    refine Subtype.ext ?_
    funext j
    refine Subtype.ext ?_
    have h := BoundedClassPower.gateOfLabel_pow_eq_one lbl j
    have hcoe : (((u ^ (lbl.1.val + 1) :
        ClassificationLevels.diagonalSymmetryGroup
          (GlobalClassificationBridge.exactCodeProjector C)) :
        ClassificationLevels.LocalPhase 6) j : ℂ)
        = ((u : ClassificationLevels.LocalPhase 6) j : ℂ) ^ (lbl.1.val + 1) := by
      simp [Pi.pow_apply, SubmonoidClass.coe_pow]
    rw [hcoe, hgate, h]
    rfl
  have hdvd : orderOf g ∣ lbl.1.val + 1 := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← hclass, ClassificationLevels.intrinsicClass, ← QuotientGroup.mk_pow,
      hpow]
    rfl
  have hlt : lbl.1.val + 1 ≤ 9 := lbl.1.isLt
  exact le_trans (Nat.le_of_dvd (Nat.succ_pos _) hdvd) hlt

end

end MainTheory.SSLPCompleteness
