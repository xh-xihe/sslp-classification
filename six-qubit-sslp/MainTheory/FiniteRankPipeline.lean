import MainTheory.FinitePipeline
import MainTheory.AffineRankCertificate

/-!
# Kernel-facing active-rank rows for the finite six-qubit pipeline

The older `FinitePipeline.RankResultData` stores two unproved natural-number
rank headlines.  This module supplies the stronger row format: the pair is
explicit, the active face is checked against that same pair, and each rank is
carried by an `AffineRankCertificate.Data` object whose complete validity
predicate is checked by ordinary kernel reduction.

The finite `beta` table is deliberately guarded by its domain.  Its total
fallback is zero, and `RankRow.Valid` additionally requires both rank indices
to lie in `[0,6]`; an out-of-range index therefore cannot silently acquire a
useful cutoff.  The row also records the actual generator range `2 ≤ q ≤ 9`
and the nontrivial logical-order conditions `2 ≤ m` and `m ∣ q`.

`pairId` is provenance metadata.  Soundness is stated for the explicit
`pair`; a generated table should separately prove that each identifier maps
to this payload, just as for `FinitePipeline.CertifiedMomentRow`.  Keeping that
lookup out of `Valid` prevents a large array reduction from obscuring the
algebraic certificate check.
-/

namespace MainTheory.FiniteRankPipeline

open MainTheory.FinitePipeline

/-- The exact values used by the six-variable active-rank filter. -/
private def betaTable : Fin 7 → ℕ := ![0, 1, 1, 2, 3, 5, 9]

/-- The denominator cutoff table `(0,1,1,2,3,5,9)`.  Values outside the
proved table domain are zero, not an extrapolated or permissive cutoff. -/
def beta (r : ℕ) : ℕ :=
  if h : r < 7 then betaTable ⟨r, h⟩ else 0

@[simp] theorem beta_zero : beta 0 = 0 := by decide
@[simp] theorem beta_one : beta 1 = 1 := by decide
@[simp] theorem beta_two : beta 2 = 1 := by decide
@[simp] theorem beta_three : beta 3 = 2 := by decide
@[simp] theorem beta_four : beta 4 = 3 := by decide
@[simp] theorem beta_five : beta 5 = 5 := by decide
@[simp] theorem beta_six : beta 6 = 9 := by decide

theorem beta_eq_zero_of_out_of_range {r : ℕ} (h : 7 ≤ r) : beta r = 0 := by
  simp [beta, Nat.not_lt.mpr h]

/-- One complete active-face/rank row.  There are no separate rank headlines:
`rank0.rank` and `rank1.rank` are the advertised numbers, so a headline cannot
drift away from the certificate that proves it. -/
structure RankRow where
  pairId : ℕ
  pair : FiberPair
  face : FaceData
  rank0 : AffineRankCertificate.Data
  rank1 : AffineRankCertificate.Data
  compatible : Bool
  deriving Repr

/-- The rank used by the refined denominator cutoff. -/
def RankRow.commonRank (row : RankRow) : ℕ :=
  min row.rank0.rank row.rank1.rank

/-- The exact arithmetic condition represented by the Boolean flag. -/
def RankRow.CompatibilityCondition (row : RankRow) : Prop :=
  row.pair.q ≤ beta row.commonRank

instance (row : RankRow) : Decidable row.CompatibilityCondition := by
  unfold RankRow.CompatibilityCondition
  infer_instance

/-- Complete validity of a rank row.  In addition to the mathematical
certificates, the explicit bounds ensure that neither `beta` nor a malformed
`q,m` sector is used outside the finite reduction proved in the paper. -/
structure RankRow.Valid (row : RankRow) : Prop where
  face_valid : row.face.Valid row.pair
  rank0_valid : row.rank0.Valid row.face.active0
  rank1_valid : row.rank1.Valid row.face.active1
  rank0_in_range : row.rank0.rank ≤ 6
  rank1_in_range : row.rank1.rank ≤ 6
  q_lower : 2 ≤ row.pair.q
  q_upper : row.pair.q ≤ beta 6
  m_lower : 2 ≤ row.pair.m
  m_dvd_q : row.pair.m ∣ row.pair.q
  compatible_exact : row.compatible = true ↔ row.CompatibilityCondition

private def ValidConditions (row : RankRow) : Prop :=
  row.face.Valid row.pair ∧
  row.rank0.Valid row.face.active0 ∧
  row.rank1.Valid row.face.active1 ∧
  row.rank0.rank ≤ 6 ∧ row.rank1.rank ≤ 6 ∧
  2 ≤ row.pair.q ∧ row.pair.q ≤ beta 6 ∧
  2 ≤ row.pair.m ∧ row.pair.m ∣ row.pair.q ∧
  (row.compatible = true ↔ row.CompatibilityCondition)

private theorem validConditions_iff (row : RankRow) :
    ValidConditions row ↔ row.Valid := by
  constructor
  · rintro ⟨hf, hr0, hr1, hr0b, hr1b, hql, hqu, hml, hmd, hc⟩
    exact ⟨hf, hr0, hr1, hr0b, hr1b, hql, hqu, hml, hmd, hc⟩
  · intro h
    exact ⟨h.face_valid, h.rank0_valid, h.rank1_valid,
      h.rank0_in_range, h.rank1_in_range, h.q_lower, h.q_upper,
      h.m_lower, h.m_dvd_q, h.compatible_exact⟩

instance (row : RankRow) : Decidable row.Valid := by
  letI : Decidable (ValidConditions row) := by
    unfold ValidConditions
    infer_instance
  exact decidable_of_iff (ValidConditions row) (validConditions_iff row)

/-- The intrinsic statement that the two advertised masks are exactly the
coordinates which can be positive at some feasible moment point. -/
def RankRow.ActiveMasksExact (row : RankRow) : Prop :=
  (∀ x, InMask row.face.active0 x ↔
      ∃ p0 p1, Feasible row.pair p0 p1 ∧ 0 < p0 x) ∧
  (∀ x, InMask row.face.active1 x ↔
      ∃ p0 p1, Feasible row.pair p0 p1 ∧ 0 < p1 x)

theorem RankRow.activeMasksExact_of_valid {row : RankRow} (h : row.Valid) :
    row.ActiveMasksExact :=
  active_masks_exact h.face_valid

theorem RankRow.rank0_eq_of_valid {row : RankRow} (h : row.Valid) :
    AffineRankCertificate.maskAffineRank row.face.active0 = row.rank0.rank :=
  AffineRankCertificate.affineRank_eq_of_valid h.rank0_valid

theorem RankRow.rank1_eq_of_valid {row : RankRow} (h : row.Valid) :
    AffineRankCertificate.maskAffineRank row.face.active1 = row.rank1.rank :=
  AffineRankCertificate.affineRank_eq_of_valid h.rank1_valid

theorem RankRow.compatible_iff_of_valid {row : RankRow} (h : row.Valid) :
    row.compatible = true ↔
      row.pair.q ≤ beta (min row.rank0.rank row.rank1.rank) := by
  simpa only [RankRow.CompatibilityCondition, RankRow.commonRank] using
    h.compatible_exact

/-- Compatibility rewritten using the two mathematically certified affine
ranks, rather than even the certificate payload's rank fields. -/
theorem RankRow.compatible_iff_actualRanks_of_valid {row : RankRow}
    (h : row.Valid) :
    row.compatible = true ↔
      row.pair.q ≤ beta
        (min (AffineRankCertificate.maskAffineRank row.face.active0)
          (AffineRankCertificate.maskAffineRank row.face.active1)) := by
  rw [row.rank0_eq_of_valid h, row.rank1_eq_of_valid h]
  exact row.compatible_iff_of_valid h

/-- All semantic consequences consumed by the later finite enumeration. -/
structure RankRow.Sound (row : RankRow) : Prop where
  active_masks_exact : row.ActiveMasksExact
  rank0_exact :
    AffineRankCertificate.maskAffineRank row.face.active0 = row.rank0.rank
  rank1_exact :
    AffineRankCertificate.maskAffineRank row.face.active1 = row.rank1.rank
  compatibility_iff :
    row.compatible = true ↔
      row.pair.q ≤ beta
        (min (AffineRankCertificate.maskAffineRank row.face.active0)
          (AffineRankCertificate.maskAffineRank row.face.active1))
  rank0_in_range : row.rank0.rank ≤ 6
  rank1_in_range : row.rank1.rank ≤ 6
  q_lower : 2 ≤ row.pair.q
  q_upper : row.pair.q ≤ 9
  m_lower : 2 ≤ row.pair.m
  m_dvd_q : row.pair.m ∣ row.pair.q

/-- **A valid raw row has the complete active-face/rank meaning claimed by
the finite pipeline.** -/
theorem RankRow.sound_of_valid {row : RankRow} (h : row.Valid) : row.Sound where
  active_masks_exact := row.activeMasksExact_of_valid h
  rank0_exact := row.rank0_eq_of_valid h
  rank1_exact := row.rank1_eq_of_valid h
  compatibility_iff := row.compatible_iff_actualRanks_of_valid h
  rank0_in_range := h.rank0_in_range
  rank1_in_range := h.rank1_in_range
  q_lower := h.q_lower
  q_upper := by simpa using h.q_upper
  m_lower := h.m_lower
  m_dvd_q := h.m_dvd_q

/-- A generated row together with its ordinary kernel-checked validity proof. -/
structure CertifiedRankRow where
  row : RankRow
  valid : row.Valid

/-- **Proof-carrying rank rows are semantically sound.** -/
theorem CertifiedRankRow.sound (cert : CertifiedRankRow) : cert.row.Sound :=
  cert.row.sound_of_valid cert.valid

end MainTheory.FiniteRankPipeline
