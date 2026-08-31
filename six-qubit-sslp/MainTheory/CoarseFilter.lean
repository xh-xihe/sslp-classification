import MainTheory.AffineRankCertificate
import MainTheory.BinaryBeta

/-!
# The affine--Smith coarse filter

This file formalizes the *semantic* content of the inexpensive filter in
`main.tex`: if a genuine primitive lift has actual support rank `r`, then the
affine ranks of both full residue fibres must be large enough for its physical
denominator `q`.

There are two deliberately separate inputs.

* `ThresholdBounds` certifies that the displayed small binary denominator
  bounds really are universal `BinaryBeta.BetaBound` theorems.  The numerical
  lookup below is therefore not, by itself, accepted as mathematics.
* `PrimitiveLiftRealization` is the output expected from the preceding
  covariance and rationalization arguments.  It contains the actual support
  masks, their common affine rank, and the nonsingular binary system whose
  sharp inverse denominator is divisible by `q`.

Consequently this module does **not** claim that the still-missing
`BetaBound 6 9` proof follows from a literal table, and it does not identify a
literal list of 508 rows with the coarse image.  The function-indexed
`Directory` at the end states the exact coverage and no-ghost obligations a
generated certificate must discharge in the ordinary Lean kernel.
-/

namespace MainTheory.CoarseFilter

open MainTheory.FinitePipeline
open MainTheory.AffineRankCertificate
open MainTheory.BinaryBeta
open MainTheory.SharpClearing

/-! ## The paper's small threshold and `r_min` -/

/-- The displayed six-variable binary-Smith upper bounds.  Returning zero
outside `[0,6]` makes accidental use beyond the certified domain fail closed. -/
def threshold : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 5
  | 6 => 9
  | _ => 0

/-- The paper's smallest possible affine rank for the nontrivial range
`2 ≤ q ≤ 9`.  The values outside that range are totality conventions:
small/trivial denominators return one and values above the proved six-variable
cutoff return seven. -/
def rMin (q : ℕ) : ℕ :=
  if q ≤ 1 then 1
  else if q ≤ 2 then 3
  else if q ≤ 3 then 4
  else if q ≤ 5 then 5
  else if q ≤ 9 then 6
  else 7

@[simp] theorem rMin_two : rMin 2 = 3 := by decide
@[simp] theorem rMin_three : rMin 3 = 4 := by decide
@[simp] theorem rMin_four : rMin 4 = 5 := by decide
@[simp] theorem rMin_five : rMin 5 = 5 := by decide
@[simp] theorem rMin_six : rMin 6 = 6 := by decide
@[simp] theorem rMin_seven : rMin 7 = 6 := by decide
@[simp] theorem rMin_eight : rMin 8 = 6 := by decide
@[simp] theorem rMin_nine : rMin 9 = 6 := by decide

/-- The finite table implication used by the coarse filter.  Notice that the
premise is an actual upper-bound inequality; a table entry alone cannot create
that premise. -/
theorem rMin_le_of_le_threshold {q r : ℕ}
    (hq : 2 ≤ q) (hr : r ≤ 6) (hqr : q ≤ threshold r) :
    rMin q ≤ r := by
  by_cases h1 : q ≤ 1
  · omega
  by_cases h2 : q ≤ 2
  · simp [rMin, h1, h2]
    interval_cases r <;> simp [threshold] at hqr ⊢ <;> omega
  by_cases h3 : q ≤ 3
  · simp [rMin, h1, h2, h3]
    interval_cases r <;> simp [threshold] at hqr ⊢ <;> omega
  by_cases h5 : q ≤ 5
  · simp [rMin, h1, h2, h3, h5]
    interval_cases r <;> simp [threshold] at hqr ⊢ <;> omega
  by_cases h9 : q ≤ 9
  · simp [rMin, h1, h2, h3, h5, h9]
    interval_cases r <;> simp [threshold] at hqr ⊢ <;> omega
  · interval_cases r <;> simp [threshold] at hqr <;> omega

/-- A proof object for the *semantic* upper halves of the displayed table.
Future binary-matrix certificates should construct this object. -/
structure ThresholdBounds : Prop where
  upper : ∀ r, 1 ≤ r → r ≤ 6 → BetaBound r (threshold r)

/-! ## Actual supports versus full fibres -/

/-- Inclusion of six-bit masks implies monotonicity of their exact affine
rank.  This is the formal step from actual nonzero supports to full fibres. -/
theorem maskAffineRank_mono {small large : ℕ}
    (hsub : ∀ x, InMask small x → InMask large x) :
    maskAffineRank small ≤ maskAffineRank large := by
  apply Submodule.finrank_mono
  apply AffineSubspace.direction_le
  apply affineSpan_mono ℚ
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hsub x hx, rfl⟩

/-- The precise interface supplied by the common-covariance and binary-simplex
rationalization proof for one genuine code/lift.  In particular, merely
exhibiting two full-fibre masks is not enough to construct this witness. -/
structure PrimitiveLiftRealization (pair : FiberPair) where
  rank : ℕ
  rank_pos : 1 ≤ rank
  rank_le_six : rank ≤ 6
  support0 : ℕ
  support1 : ℕ
  support0_subset : ∀ x, InMask support0 x → InMask pair.mask0 x
  support1_subset : ∀ x, InMask support1 x → InMask pair.mask1 x
  support0_rank : maskAffineRank support0 = rank
  support1_rank : maskAffineRank support1 = rank
  binarySystem : Matrix (Fin rank) (Fin rank) ℤ
  binary : IsZeroOne binarySystem
  nonsingular : binarySystem.det ≠ 0
  q_lower : 2 ≤ pair.q
  q_dvd_denominator : pair.q ∣ inverseDenominator binarySystem

/-- Propositional packaging for theorem statements which assert existence of
a primitive-lift realization without choosing its support masks or binary
system.  The data-carrying structure itself must live in `Type`: putting it in
`Prop` would erase precisely the rank and matrix consumed by the soundness
proof. -/
abbrev HasPrimitiveLiftRealization (pair : FiberPair) : Prop :=
  Nonempty (PrimitiveLiftRealization pair)

/-- The intrinsic full-fibre predicate in equation (coarserank). -/
def FullFiberCriterion (pair : FiberPair) : Prop :=
  rMin pair.q ≤
    min (maskAffineRank pair.mask0) (maskAffineRank pair.mask1)

/-! ## Exact affine-rank rows -/

/-- One generated pair of exact full-fibre affine-rank certificates. -/
structure FullFiberRankRow where
  rank0 : AffineRankCertificate.Data
  rank1 : AffineRankCertificate.Data
  deriving Repr

/-- The cheap decidable headline checked in generated shards. -/
def FullFiberRankRow.Passes (pair : FiberPair) (row : FullFiberRankRow) : Prop :=
  rMin pair.q ≤ min row.rank0.rank row.rank1.rank

instance (pair : FiberPair) (row : FullFiberRankRow) : Decidable (row.Passes pair) := by
  unfold FullFiberRankRow.Passes
  infer_instance

/-- A row is valid only when both advertised ranks are complete lower-and-upper
certificates for the two masks in that same explicit pair. -/
structure FullFiberRankRow.ValidFor (pair : FiberPair)
    (row : FullFiberRankRow) : Prop where
  rank0_valid : row.rank0.Valid pair.mask0
  rank1_valid : row.rank1.Valid pair.mask1

/-- A valid generated headline is exactly the semantic full-fibre criterion,
not merely a comparison of two unproved rank numerals. -/
theorem FullFiberRankRow.passes_iff_fullFiberCriterion
    {pair : FiberPair} {row : FullFiberRankRow} (h : row.ValidFor pair) :
    row.Passes pair ↔ FullFiberCriterion pair := by
  unfold FullFiberRankRow.Passes FullFiberCriterion
  rw [affineRank_eq_of_valid h.rank0_valid,
    affineRank_eq_of_valid h.rank1_valid]

/-- **Soundness of the coarse filter.**  Every genuine realization satisfying
the semantic binary denominator bounds passes the criterion for the two full
fibres.  This proof uses the actual support rank directly and consequently
does not require exact affine-rank certificates for either full fibre. -/
theorem fullFiberCriterion_of_realization
    (bounds : ThresholdBounds) {pair : FiberPair}
    (real : PrimitiveLiftRealization pair) :
    FullFiberCriterion pair := by
  have hden_le : inverseDenominator real.binarySystem ≤ threshold real.rank :=
    bounds.upper real.rank real.rank_pos real.rank_le_six
      real.rank real.rank_pos (Nat.le_refl _)
      real.binarySystem real.binary real.nonsingular
  have hq_le_den : pair.q ≤ inverseDenominator real.binarySystem :=
    Nat.le_of_dvd (inverseDenominator_pos real.binarySystem)
      real.q_dvd_denominator
  have hqRank : pair.q ≤ threshold real.rank := hq_le_den.trans hden_le
  have hmin : rMin pair.q ≤ real.rank :=
    rMin_le_of_le_threshold real.q_lower real.rank_le_six hqRank
  have hr0 : real.rank ≤ maskAffineRank pair.mask0 := by
    rw [← real.support0_rank]
    exact maskAffineRank_mono real.support0_subset
  have hr1 : real.rank ≤ maskAffineRank pair.mask1 := by
    rw [← real.support1_rank]
    exact maskAffineRank_mono real.support1_subset
  unfold FullFiberCriterion
  exact Nat.le_min.mpr ⟨hmin.trans hr0, hmin.trans hr1⟩

/-- Existential/propositional form of `fullFiberCriterion_of_realization`. -/
theorem fullFiberCriterion_of_exists_realization
    (bounds : ThresholdBounds) {pair : FiberPair}
    (real : HasPrimitiveLiftRealization pair) :
    FullFiberCriterion pair := by
  rcases real with ⟨real⟩
  exact fullFiberCriterion_of_realization bounds real

/-! ## Threshold-only witnesses

The 11,422-row coarse audit does not need 22,844 complete affine-rank
certificates.  Passing a threshold is one-sided: a lower certificate of rank
at least `rMin q` suffices.  Failing is also one-sided: an upper certificate of
rank strictly below `rMin q` on either colour suffices.
-/

/-- Two one-sided lower certificates prove that a pair passes.  Their declared
ranks may equal the threshold or be larger; no upper-rank data is required. -/
structure KeepWitness (pair : FiberPair) where
  data0 : AffineRankCertificate.Data
  data1 : AffineRankCertificate.Data
  lower0 : LowerInverseValid pair.mask0 data0
  lower1 : LowerInverseValid pair.mask1 data1
  threshold0 : rMin pair.q ≤ data0.rank
  threshold1 : rMin pair.q ≤ data1.rank

theorem KeepWitness.fullFiberCriterion {pair : FiberPair}
    (w : KeepWitness pair) : FullFiberCriterion pair := by
  unfold FullFiberCriterion
  apply Nat.le_min.mpr
  constructor
  · exact w.threshold0.trans
      (rank_le_maskAffineRank_of_lowerInverse w.lower0)
  · exact w.threshold1.trans
      (rank_le_maskAffineRank_of_lowerInverse w.lower1)

/-- An upper certificate on the left colour proves rejection.  It contains no
unneeded lower-rank minor. -/
structure RejectLeftWitness (pair : FiberPair) where
  data : AffineRankCertificate.Data
  upper : UpperListInverseValid pair.mask0 data
  below : data.rank < rMin pair.q

theorem RejectLeftWitness.not_fullFiberCriterion {pair : FiberPair}
    (w : RejectLeftWitness pair) : ¬ FullFiberCriterion pair := by
  intro h
  unfold FullFiberCriterion at h
  have hleft : rMin pair.q ≤ maskAffineRank pair.mask0 :=
    (Nat.le_min.mp h).1
  have hupper : maskAffineRank pair.mask0 ≤ w.data.rank :=
    maskAffineRank_le_rank_of_upperListInverse w.upper
  exact (Nat.not_lt_of_ge (hleft.trans hupper)) w.below

/-- Symmetric one-sided rejection certificate for the right colour. -/
structure RejectRightWitness (pair : FiberPair) where
  data : AffineRankCertificate.Data
  upper : UpperListInverseValid pair.mask1 data
  below : data.rank < rMin pair.q

theorem RejectRightWitness.not_fullFiberCriterion {pair : FiberPair}
    (w : RejectRightWitness pair) : ¬ FullFiberCriterion pair := by
  intro h
  unfold FullFiberCriterion at h
  have hright : rMin pair.q ≤ maskAffineRank pair.mask1 :=
    (Nat.le_min.mp h).2
  have hupper : maskAffineRank pair.mask1 ≤ w.data.rank :=
    maskAffineRank_le_rank_of_upperListInverse w.upper
  exact (Nat.not_lt_of_ge (hright.trans hupper)) w.below

/-- Exactly one proof-producing branch is stored for each input. -/
inductive DecisionWitness (pair : FiberPair) where
  | keep (witness : KeepWitness pair)
  | rejectLeft (witness : RejectLeftWitness pair)
  | rejectRight (witness : RejectRightWitness pair)

def DecisionWitness.kept {pair : FiberPair} : DecisionWitness pair → Bool
  | .keep _ => true
  | .rejectLeft _ => false
  | .rejectRight _ => false

/-- The Boolean decision is unchanged when its proof payload is transported
along an equality of pair indices.  Generated directory joins need this
explicitly: the witness type is dependent even though `kept` only records its
constructor. -/
@[simp] theorem DecisionWitness.kept_transport
    {pair pair' : FiberPair} (h : pair = pair')
    (w : DecisionWitness pair) :
    (h ▸ w).kept = w.kept := by
  cases h
  rfl

@[simp] theorem DecisionWitness.kept_cast
    {pair pair' : FiberPair} (h : pair = pair')
    (w : DecisionWitness pair) :
    (cast (congrArg DecisionWitness h) w).kept = w.kept := by
  cases h
  rfl

/-- A threshold-only decision has exactly the intrinsic mathematical meaning
of the coarse affine-rank test. -/
theorem DecisionWitness.kept_iff_fullFiberCriterion
    {pair : FiberPair} (w : DecisionWitness pair) :
    w.kept = true ↔ FullFiberCriterion pair := by
  cases w with
  | keep witness =>
      constructor
      · intro _
        exact witness.fullFiberCriterion
      · intro _
        rfl
  | rejectLeft witness =>
      constructor
      · intro h
        simp [DecisionWitness.kept] at h
      · intro h
        exact (witness.not_fullFiberCriterion h).elim
  | rejectRight witness =>
      constructor
      · intro h
        simp [DecisionWitness.kept] at h
      · intro h
        exact (witness.not_fullFiberCriterion h).elim

/-! ## A resource-safe exact generated directory -/

/-- Function-indexed data for an exact coarse-filter image.  The output table
contains only bounded source indices; `outputAt` is therefore definitionally
an input row and cannot be a ghost payload copied from somewhere else.

`outputOfInput` is an explicit partial inverse.  It lets generated shards
prove coverage and injectivity by local round trips, without reducing a giant
array, sorting a giant list, or searching 508 outputs for each of 11,422
inputs.  `decisionAt` stores only the one-sided witness required by that row. -/
structure Directory (inputCount outputCount : ℕ) where
  inputAt : Fin inputCount → FiberPair
  decisionAt : (i : Fin inputCount) → DecisionWitness (inputAt i)
  outputSource : Fin outputCount → Fin inputCount
  outputOfInput : Fin inputCount → Option (Fin outputCount)

def Directory.keepAt {inputCount outputCount : ℕ}
    (d : Directory inputCount outputCount) (i : Fin inputCount) : Bool :=
  (d.decisionAt i).kept

def Directory.outputAt {inputCount outputCount : ℕ}
    (d : Directory inputCount outputCount) (j : Fin outputCount) : FiberPair :=
  d.inputAt (d.outputSource j)

/-- Exact per-row meaning plus a two-sided source-directory audit. -/
structure Directory.Valid {inputCount outputCount : ℕ}
    (d : Directory inputCount outputCount) : Prop where
  lookup_defined_exact : ∀ i,
    (d.outputOfInput i).isSome = d.keepAt i
  source_lookup : ∀ j,
    d.outputOfInput (d.outputSource j) = some j
  lookup_source : ∀ i j,
    d.outputOfInput i = some j → d.outputSource j = i

/-- Generated keep flags state exactly the intrinsic full-fibre criterion. -/
theorem Directory.Valid.keep_iff_fullFiberCriterion
    {inputCount outputCount : ℕ} {d : Directory inputCount outputCount}
    (_h : d.Valid) (i : Fin inputCount) :
    d.keepAt i = true ↔ FullFiberCriterion (d.inputAt i) := by
  exact (d.decisionAt i).kept_iff_fullFiberCriterion

/-- Every output is retained; hence the output directory has no ghost row. -/
theorem Directory.Valid.output_kept
    {inputCount outputCount : ℕ} {d : Directory inputCount outputCount}
    (h : d.Valid) (j : Fin outputCount) :
    d.keepAt (d.outputSource j) = true := by
  rw [← h.lookup_defined_exact (d.outputSource j)]
  simp [h.source_lookup j]

/-- Every retained input occurs in the output directory. -/
theorem Directory.Valid.kept_covered
    {inputCount outputCount : ℕ} {d : Directory inputCount outputCount}
    (h : d.Valid) (i : Fin inputCount) (hi : d.keepAt i = true) :
    ∃ j, d.outputSource j = i := by
  have hsome : (d.outputOfInput i).isSome = true := by
    rw [h.lookup_defined_exact i, hi]
  cases hout : d.outputOfInput i with
  | none => simp [hout] at hsome
  | some j =>
      exact ⟨j, h.lookup_source i j hout⟩

/-- Distinct output rows cannot secretly refer to the same labeled input. -/
theorem Directory.Valid.outputSource_injective
    {inputCount outputCount : ℕ} {d : Directory inputCount outputCount}
    (h : d.Valid) : Function.Injective d.outputSource := by
  intro j k hjk
  have hj := h.source_lookup j
  have hk := h.source_lookup k
  rw [hjk, hk] at hj
  exact (Option.some.inj hj).symm

/-- No genuine realization is discarded, and exact coverage supplies its
source occurrence in the generated output directory. -/
theorem Directory.Valid.realization_retained
    {inputCount outputCount : ℕ} {d : Directory inputCount outputCount}
    (h : d.Valid) (bounds : ThresholdBounds) (i : Fin inputCount)
    (real : PrimitiveLiftRealization (d.inputAt i)) :
    d.keepAt i = true ∧ ∃ j, d.outputSource j = i := by
  have hcriterion := fullFiberCriterion_of_realization bounds real
  have hkeep := (h.keep_iff_fullFiberCriterion i).2 hcriterion
  exact ⟨hkeep, h.kept_covered i hkeep⟩

/-- The paper's claimed finite reduction has this type.  Constructing a value
of `Valid` is the proof; the two numerals alone prove nothing. -/
abbrev PaperDirectory := Directory 11422 508

end MainTheory.CoarseFilter
