import MainTheory.Orbit31ExactSupportClassification
import MainTheory.Generated.Orbit31NoSingletonCounts

/-! The exact second support-audit count concerns real feasible supports. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
namespace MainTheory.Orbit31NoSingletonClassification
open MainTheory.Orbit31ExactSupportClassification
open MainTheory.Orbit31SupportCoverageBase
open MainTheory.Orbit31SignedSupport
open MainTheory.Generated.Orbit31SupportCoverage
open scoped BigOperators
noncomputable section

def HasSupportWithoutSingleton (mask : Fin 65536) : Prop :=
  HasSupport mask ∧ NoSingleton mask.val

def supportEquiv : {pair : Fin 16 × Fin 4096 //
    isPrimal (Aggregate.certificates pair.1 pair.2) = true ∧
      noSingleton (4096*pair.1.val+pair.2.val) = true} ≃
    {mask : Fin 65536 // HasSupportWithoutSingleton mask} :=
  Equiv.subtypeEquiv (finProdFinEquiv : Fin 16 × Fin 4096 ≃ Fin 65536) (fun pair => by
    have h := and_congr (block_classification pair.1 pair.2).symm
      (noSingleton_iff (4096*pair.1.val+pair.2.val))
    simpa only [HasSupportWithoutSingleton,finProdFinEquiv,Nat.add_comm] using h)

theorem exact_support_count :
    Nat.card {mask : Fin 65536 // HasSupportWithoutSingleton mask} = 2903 := by
  classical
  calc
    _ = Nat.card {pair : Fin 16 × Fin 4096 //
        isPrimal (Aggregate.certificates pair.1 pair.2) = true ∧
          noSingleton (4096*pair.1.val+pair.2.val) = true} :=
      Nat.card_congr supportEquiv.symm
    _ = Nat.card (Σ i : Fin 16, {j : Fin 4096 //
        isPrimal (Aggregate.certificates i j) = true ∧
          noSingleton (4096*i.val+j.val) = true}) :=
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
        (fun (i : Fin 16) (j : Fin 4096) =>
          isPrimal (Aggregate.certificates i j) = true ∧ noSingleton (4096*i.val+j.val) = true))
    _ = ∑ i : Fin 16, (Finset.univ.filter fun j : Fin 4096 =>
        isPrimal (Aggregate.certificates i j) = true ∧
          noSingleton (4096*i.val+j.val) = true).card := by
      rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
      simp_rw [Fintype.card_subtype]
    _ = ∑ i, MainTheory.Generated.Orbit31NoSingletonCounts.counts i :=
      Finset.sum_congr rfl (fun i _ => MainTheory.Generated.Orbit31NoSingletonCounts.count i)
    _ = 2903 := MainTheory.Generated.Orbit31NoSingletonCounts.count_total

end
end MainTheory.Orbit31NoSingletonClassification
