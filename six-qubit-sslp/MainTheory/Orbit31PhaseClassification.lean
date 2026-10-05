import MainTheory.Orbit31NoSingletonClassification
import MainTheory.Generated.Orbit31PhaseCoverage.Aggregate
import MainTheory.Orbit31PhysicalSupportFilters

/-! Complete signed-cycle classification with real moment semantics.
The 2903 records exhaust the second-stage set by inclusion and equal cardinality.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
namespace MainTheory.Orbit31PhaseClassification
open MainTheory.Orbit31NoSingletonClassification (HasSupportWithoutSingleton)
open MainTheory.Orbit31PhaseCoverageBase
open MainTheory.Orbit31SignedSupport
open MainTheory.Generated.Orbit31PhaseCoverage
noncomputable section

def stageOne : Finset (Fin 65536) := by
  classical
  exact Finset.univ.filter HasSupportWithoutSingleton

theorem mem_stageOne (mask : Fin 65536) : mask ∈ stageOne ↔ HasSupportWithoutSingleton mask := by
  simp [stageOne]

theorem stageOne_card : stageOne.card = 2903 := by
  calc
    _ = Nat.card {mask : Fin 65536 // HasSupportWithoutSingleton mask} :=
      (Nat.subtype_card stageOne mem_stageOne).symm
    _ = 2903 := MainTheory.Orbit31NoSingletonClassification.exact_support_count

def recordMasks : Finset (Fin 65536) := (Aggregate.records.map Entry.mask).toFinset

theorem recordMasks_card : recordMasks.card = 2903 := by
  rw [recordMasks,List.toFinset_card_of_nodup Aggregate.masks_nodup,List.length_map,Aggregate.length]

theorem records_exhaust_stageOne : recordMasks = stageOne := by
  apply Finset.eq_of_subset_of_card_le
  · intro mask hm
    obtain ⟨entry,he,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    subst mask
    have hv := Aggregate.valid entry he
    exact (mem_stageOne entry.mask).mpr ⟨real_feasible hv,hv.2.2.1⟩
  · rw [stageOne_card,recordMasks_card]

def survivorMasks : Finset (Fin 65536) :=
  ((Aggregate.records.filter fun entry => isColoring entry.phase).map Entry.mask).toFinset

theorem survivorMasks_card : survivorMasks.card = 311 := by
  have hsub : ((Aggregate.records.filter fun entry => isColoring entry.phase).map Entry.mask).Sublist
      (Aggregate.records.map Entry.mask) := List.filter_sublist.map Entry.mask
  have hn := Aggregate.masks_nodup.sublist hsub
  rw [survivorMasks,List.toFinset_card_of_nodup hn,List.length_map,Aggregate.color_count]

def HasSurvivingSupport (mask : Fin 65536) : Prop :=
  HasSupportWithoutSingleton mask ∧ GraphCompatible mask.val

theorem survivor_iff (mask : Fin 65536) : mask ∈ survivorMasks ↔ HasSurvivingSupport mask := by
  constructor
  · intro hm
    obtain ⟨entry,he,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    subst mask
    obtain ⟨he,hcolor⟩ := List.mem_filter.mp he
    have hv := Aggregate.valid entry he
    exact ⟨⟨real_feasible hv,hv.2.2.1⟩,(graph_iff hv).mpr hcolor⟩
  · rintro ⟨hstage,hgraph⟩
    have hm := (mem_stageOne mask).mpr hstage
    rw [← records_exhaust_stageOne] at hm
    obtain ⟨entry,he,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    subst mask
    have hv := Aggregate.valid entry he
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨entry,List.mem_filter.mpr ⟨he,(graph_iff hv).mp hgraph⟩,rfl⟩)

theorem exact_support_count : Nat.card {mask : Fin 65536 // HasSurvivingSupport mask} = 311 := by
  rw [Nat.subtype_card survivorMasks survivor_iff,survivorMasks_card]

theorem exact_count_chain :
    Nat.card {mask : Fin 65536 // MainTheory.Orbit31ExactSupportClassification.HasSupport mask} = 15603 ∧
    Nat.card {mask : Fin 65536 // HasSupportWithoutSingleton mask} = 2903 ∧
    Nat.card {mask : Fin 65536 // HasSurvivingSupport mask} = 311 :=
  ⟨MainTheory.Orbit31ExactSupportClassification.exact_support_count,
    MainTheory.Orbit31NoSingletonClassification.exact_support_count,exact_support_count⟩

theorem physical_survivor (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit31.S0 → c x = 0)
    (hd : ∀ x, x ∉ SixQubit.Orbit31.S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) (mask : Fin 65536)
    (hm : MainTheory.MatrixPositiveSupportCertificates.ExactSupport
      (MainTheory.Orbit31SupportSemantics.maskSet mask.val)
      (MainTheory.Orbit31SupportBase.probabilities c)) : mask ∈ survivorMasks := by
  apply (survivor_iff mask).mpr
  have hf := MainTheory.Orbit31PhysicalSupportFilters.physical_filters c d hc hd hnc hnd hkl mask.val hm
  exact ⟨⟨⟨MainTheory.Orbit31SupportBase.probabilities c,
    MainTheory.Orbit31SupportBase.physical_balanced c d hc hd hnc hnd hkl,hm⟩,hf.1⟩,
    ⟨MainTheory.Orbit31PhaseRatios.sigma (MainTheory.Orbit31PhaseRatios.C c)
      (MainTheory.Orbit31PhaseRatios.D d),hf.2⟩⟩

end
end MainTheory.Orbit31PhaseClassification
