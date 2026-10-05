import MainTheory.Generated.Orbit31SupportCoverage.Aggregate

/-! Complete support classification for the actual seven balanced moments.
The theorem concerns all real probability vectors and every boundary support.
-/
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000

namespace MainTheory.Orbit31ExactSupportClassification
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.Orbit31SupportBase
open MainTheory.Orbit31SupportSemantics
open MainTheory.Orbit31SupportCoverageBase
open MainTheory.Generated.Orbit31SupportCoverage
open scoped BigOperators
noncomputable section

def HasSupport (mask : Fin 65536) : Prop :=
  ∃ p, Feasible M b p ∧ ExactSupport (maskSet mask.val) p

def coordinates : Fin 65536 ≃ Fin 16 × Fin 4096 :=
  (finProdFinEquiv : Fin 16 × Fin 4096 ≃ Fin 65536).symm

def certificate (mask : Fin 65536) : Certificate :=
  Aggregate.certificates (coordinates mask).1 (coordinates mask).2

theorem block_classification (i : Fin 16) (j : Fin 4096) :
    HasSupport (finProdFinEquiv (i,j)) ↔
      isPrimal (Aggregate.certificates i j) = true := by
  have hv := feasible_iff (Aggregate.valid i j)
  simpa only [HasSupport,finProdFinEquiv,Nat.add_comm] using hv

theorem classification (mask : Fin 65536) :
    HasSupport mask ↔ isPrimal (certificate mask) = true := by
  have h := block_classification (coordinates mask).1 (coordinates mask).2
  simpa only [certificate,coordinates,Prod.mk.eta,Equiv.apply_symm_apply] using h

def supportEquiv : {mask : Fin 65536 // HasSupport mask} ≃
    {pair : Fin 16 × Fin 4096 // isPrimal (Aggregate.certificates pair.1 pair.2) = true} :=
  Equiv.subtypeEquiv coordinates classification

theorem exact_support_count :
    Nat.card {mask : Fin 65536 // HasSupport mask} = 15603 := by
  classical
  calc
    _ = Nat.card {pair : Fin 16 × Fin 4096 //
        isPrimal (Aggregate.certificates pair.1 pair.2) = true} :=
      Nat.card_congr supportEquiv
    _ = Nat.card (Σ i : Fin 16, {j : Fin 4096 //
        isPrimal (Aggregate.certificates i j) = true}) :=
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
        (fun (i : Fin 16) (j : Fin 4096) => isPrimal (Aggregate.certificates i j) = true))
    _ = ∑ i : Fin 16, (Finset.univ.filter fun j : Fin 4096 =>
        isPrimal (Aggregate.certificates i j) = true).card := by
      rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
      simp_rw [Fintype.card_subtype]
    _ = ∑ i, Aggregate.counts i := Finset.sum_congr rfl (fun i _ => Aggregate.count i)
    _ = 15603 := Aggregate.count_total

theorem physical_support_classified (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit31.S0 → c x = 0)
    (hd : ∀ x, x ∉ SixQubit.Orbit31.S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) (mask : Fin 65536)
    (hs : ExactSupport (maskSet mask.val) (probabilities c)) :
    isPrimal (certificate mask) = true :=
  (classification mask).mp ⟨probabilities c,physical_balanced c d hc hd hnc hnd hkl,hs⟩

end
end MainTheory.Orbit31ExactSupportClassification
