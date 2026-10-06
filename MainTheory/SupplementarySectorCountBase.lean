import MainTheory.StageRecordCounts
import MainTheory.OrbitRecordMultiplicity
import MainTheory.Generated.FinitePairDistinctness

/-!
Semantic counting helpers for the two SI sector tables. A witness list may
replace a survivor set only after kernel proofs of membership, no repetitions,
and its equality with the already established total cardinality. The sector
test always reads the actual record or full fibre-pair payload.
-/

namespace MainTheory.SupplementarySectorCountBase

open MainTheory.Generated

abbrev RecordId := Fin 12768
abbrev PairId := Fin 11422

def selectedRecords (p : RecordId → Bool) : Finset RecordId :=
  Finset.univ.filter fun r => p r

def recordSector (q m : ℕ) (r : RecordId) : Bool :=
  let a := FinitePairRecordData.generatedRecord r
  a.q == q && a.m == m

def recordCount (p : RecordId → Bool) (q m : ℕ) : ℕ :=
  ((selectedRecords p).filter fun r => recordSector q m r).card

theorem selectedRecords_card (p : RecordId → Bool) :
    (selectedRecords p).card = ((List.finRange 12768).filter p).length := by
  have hl : (List.finRange 12768).toFinset = (Finset.univ : Finset RecordId) := by
    ext i
    simp
  have hn := (List.nodup_finRange 12768).filter p
  have hc := List.toFinset_card_of_nodup hn
  rw [List.toFinset_filter, hl] at hc
  exact hc

theorem selectedRecords_eq_list (p : RecordId → Bool) (ids : List RecordId)
    (hn : ids.Nodup) (hv : ids.all p = true)
    (hc : ((List.finRange 12768).filter p).length = ids.length) :
    selectedRecords p = ids.toFinset := by
  have hs : ids.toFinset ⊆ selectedRecords p := by
    intro r hr
    have hp := List.all_eq_true.mp hv r (List.mem_toFinset.mp hr)
    simp only [selectedRecords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hp
  apply (Finset.eq_of_subset_of_card_le hs ?_).symm
  rw [selectedRecords_card, List.toFinset_card_of_nodup hn, hc]

theorem recordCount_eq_list (p : RecordId → Bool) (ids : List RecordId)
    (hn : ids.Nodup) (he : selectedRecords p = ids.toFinset) (q m : ℕ) :
    recordCount p q m = (ids.filter (recordSector q m)).length := by
  unfold recordCount
  rw [he, ← List.toFinset_filter]
  exact List.toFinset_card_of_nodup (hn.filter _)

def pairSector (q m : ℕ) (i : PairId) : Bool :=
  let p := FinitePairRecordBase.pairAtId i
  p.q == q && p.m == m

/-- Counts distinct actual full fibre-pair payloads, not merely list entries. -/
def pairCount (ids : List PairId) (q m : ℕ) : ℕ :=
  ((ids.filter (pairSector q m)).toFinset.image
    FinitePairRecordBase.pairAtId).card

theorem pairCount_eq_list (ids : List PairId) (hn : ids.Nodup) (q m : ℕ) :
    pairCount ids q m = (ids.filter (pairSector q m)).length := by
  unfold pairCount
  have hi : Function.Injective FinitePairRecordBase.pairAtId :=
    FinitePairDistinctness.pairAtId_injective
  rw [Finset.card_image_of_injective _ hi]
  exact List.toFinset_card_of_nodup (hn.filter _)

def allPairCount (q m : ℕ) : ℕ :=
  ((Finset.univ.filter fun i : PairId => pairSector q m i).image
    FinitePairRecordBase.pairAtId).card

theorem allPairCount_eq_interval (q m a b : ℕ) (hb : b ≤ 11422)
    (hs : ∀ i : PairId, pairSector q m i = true ↔ a ≤ i.val ∧ i.val < b) :
    allPairCount q m = b - a := by
  have hi : Function.Injective FinitePairRecordBase.pairAtId :=
    FinitePairDistinctness.pairAtId_injective
  unfold allPairCount
  rw [Finset.card_image_of_injective _ hi]
  have he : (Finset.univ.filter fun i : PairId => pairSector q m i).image Fin.val =
      Finset.Ico a b := by
    ext n
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨i, hp, rfl⟩
      exact (hs i).mp hp
    · intro hn
      refine ⟨⟨n, by omega⟩, ?_, rfl⟩
      exact (hs _).mpr hn
  have hc := Finset.card_image_of_injective
    (Finset.univ.filter fun i : PairId => pairSector q m i) Fin.val_injective
  rw [← hc, he, Nat.card_Ico]

end MainTheory.SupplementarySectorCountBase
