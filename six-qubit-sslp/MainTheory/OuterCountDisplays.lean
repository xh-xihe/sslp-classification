import MainTheory.OuterEnumeration
import MainTheory.SortedVectorMobius

namespace MainTheory.OuterCountDisplays

open MainTheory.OuterEnumeration

def residueMultiplicity {q : ℕ} (a : Fin 6 → Fin q) (r : Fin q) : ℕ :=
  (Finset.univ.filter fun i => a i = r).card

theorem multiplicities_sum {q : ℕ} (a : Fin 6 → Fin q) :
    ∑ r, residueMultiplicity a r = 6 := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin 6)))
    (t := Finset.univ) (f := a) (by intro i hi; simp)
  simpa only [residueMultiplicity, Finset.card_univ, Fintype.card_fin] using h.symm

theorem raw_records_divisor_formula : rawRecords.length =
    ∑ q ∈ Finset.Icc 2 9, (q.divisors.card - 1) * (q + 5).choose 6 := by
  rw [raw_records_exact]
  decide +kernel

theorem raw_count_summands :
    (List.range' 2 8).map (fun q => (q.divisors.card - 1) * (q + 5).choose 6) =
      [7, 28, 168, 210, 1386, 924, 5148, 6006] := by decide +kernel

theorem faithful_records_binomial_formula : faithfulRawRecords.length =
    ∑ q ∈ Finset.Icc 2 9, (q + 5).choose 6 := by
  rw [faithful_raw_records_exact]
  decide +kernel

theorem excess_raw_records : rawRecords.length - faithfulRawRecords.length = 7443 := by
  rw [raw_records_exact, faithful_raw_records_exact]

end MainTheory.OuterCountDisplays
