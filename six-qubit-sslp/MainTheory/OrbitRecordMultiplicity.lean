import MainTheory.ActiveRankRecordCount
import MainTheory.Generated.OrbitTableRecords
import MainTheory.Generated.FiniteOrbitCertificate

/-!
Record multiplicities of the actual labelled moment orbits.  Completeness of
the216-record witness list follows from its injection into the already certified
surviving record set of cardinal216.  The orbit labels are tied to genuine cube
action witnesses and the pairwise inequivalence of the66 directory keys.
-/

namespace MainTheory.OrbitRecordMultiplicity

open MainTheory.Generated
open MainTheory.FiniteOrbitPipeline

abbrev RecordId := Fin 12768
abbrev KeyId := Fin 66

def compatible (r : RecordId) : Bool :=
  FinitePairData.compatiblePairIds.toList.contains (FinitePairRecordData.recordPairId r).val

def compatibleRecords : Finset RecordId := Finset.univ.filter fun r => compatible r

theorem compatibleRecords_card : compatibleRecords.card = 216 := by
  have hl : (List.finRange 12768).toFinset = (Finset.univ : Finset RecordId) := by
    ext i
    simp
  have hn : ((List.finRange 12768).filter compatible).Nodup :=
    (List.nodup_finRange 12768).filter compatible
  have hc := List.toFinset_card_of_nodup hn
  rw [List.toFinset_filter, hl] at hc
  exact hc.trans MainTheory.ActiveRankRecordCount.compatible_record_count

theorem records_complete (r : RecordId) : compatible r = true ↔ ∃ i, OrbitTableRecords.record i = r := by
  have hsub : Finset.univ.image OrbitTableRecords.record ⊆ compatibleRecords := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    have h := OrbitTableRecords.facts i
    simp only [compatibleRecords, Finset.mem_filter, Finset.mem_univ, true_and, compatible]
    rw [h.1]
    exact h.2.2.1
  have hc : (Finset.univ.image OrbitTableRecords.record).card = 216 := by
    simp [Finset.card_image_of_injective _ OrbitTableRecords.record_injective]
  have he := Finset.eq_of_subset_of_card_le hsub (by rw [compatibleRecords_card, hc])
  have hm := congrArg (fun s : Finset RecordId => r ∈ s) he
  simpa [compatibleRecords] using (Iff.of_eq hm).symm

def recordPair (r : RecordId) : MainTheory.FinitePipeline.FiberPair :=
  MainTheory.OuterCompleteness.recordFiberPair (FinitePairRecordData.generatedRecord r)

def InOrbit (k : KeyId) (r : RecordId) : Prop :=
  compatible r = true ∧ MainTheory.DistanceSignature.LabeledEquivalent
    (recordPair r).q (recordPair r).m (fibersOfPair (recordPair r))
    (FiniteOrbitBase.keyAt k).q (FiniteOrbitBase.keyAt k).m (FiniteOrbitBase.keyAt k).fibers

theorem record_pair_candidate (i : Fin 216) :
    recordPair (OrbitTableRecords.record i) = FiniteOrbitBase.inputAt (OrbitTableRecords.input i) := by
  rw [recordPair, ← FinitePairRecordData.exactRecordId]
  rw [(OrbitTableRecords.facts i).1]
  exact (OrbitTableRecords.facts i).2.1

theorem input_equivalent_key_iff (i : Fin 215) (k : KeyId) :
    MainTheory.DistanceSignature.LabeledEquivalent
      (FiniteOrbitBase.inputAt i).q (FiniteOrbitBase.inputAt i).m
      (fibersOfPair (FiniteOrbitBase.inputAt i))
      (FiniteOrbitBase.keyAt k).q (FiniteOrbitBase.keyAt k).m (FiniteOrbitBase.keyAt k).fibers ↔
        (OrbitCertificate.witnessAt i).key = k := by
  have hv := OrbitCertificate.witness_valid i
  rw [OrbitCertificate.witness_input] at hv
  have hw := OrbitWitness.labeledEquivalent_of_validFor hv
  constructor
  · intro h
    by_contra hne
    have hk := MainTheory.DistanceSignature.labeledEquivalent_trans
      (MainTheory.DistanceSignature.labeledEquivalent_symm hw) h
    exact FiniteOrbitCertificate.directory_valid.keys_pairwise_inequivalent hne hk
  · intro h
    rwa [h] at hw

theorem candidate_inOrbit_iff (i : Fin 216) (k : KeyId) :
    InOrbit k (OrbitTableRecords.record i) ↔ OrbitTableRecords.key i = k := by
  have hc := (records_complete (OrbitTableRecords.record i)).2 ⟨i, rfl⟩
  simp only [InOrbit, hc, true_and, record_pair_candidate]
  rw [input_equivalent_key_iff, (OrbitTableRecords.facts i).2.2.2]

noncomputable def multiplicity (k : KeyId) : ℕ := by
  classical
  exact (Finset.univ.filter fun r => InOrbit k r).card

def assignedCount (k : KeyId) : ℕ :=
  (Finset.univ.filter fun i : Fin 216 => OrbitTableRecords.key i = k).card

theorem multiplicity_eq_assignedCount (k : KeyId) : multiplicity k = assignedCount k := by
  classical
  have he : Finset.univ.filter (fun r => InOrbit k r) =
      (Finset.univ.filter fun i : Fin 216 => OrbitTableRecords.key i = k).image OrbitTableRecords.record := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hr
      obtain ⟨i, rfl⟩ := (records_complete r).1 hr.1
      exact ⟨i, (candidate_inOrbit_iff i k).1 hr, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (candidate_inOrbit_iff i k).2 hi
  unfold multiplicity assignedCount
  rw [he, Finset.card_image_of_injective _ OrbitTableRecords.record_injective]

end MainTheory.OrbitRecordMultiplicity
