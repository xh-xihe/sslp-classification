import SixQubit.Orbit8UniversalReconstruct

/-!
# Orbit 8 universal converse, XII: weight-one Walsh rows

The `X_i` and `X_i Z_j` off-diagonal KL rows are expanded on the actual
fibres and combined by a two-row Walsh inversion.  No manuscript equation is
assumed.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

noncomputable section

def topRecip (i : Fin 6) (ij : Fin 6 × Fin 6) : SS.BitString 6 :=
  SS.bxor (edgeState ij) (SS.stdBasis i)

def touches (ij : Fin 6 × Fin 6) (j : Fin 6) : Bool :=
  (ij.1 == j) || (ij.2 == j)

theorem single_flip_intersection : ∀ i : Fin 6,
    S1.filter (fun y => SS.bxor y (SS.stdBasis i) ∈ S0) =
      insert (SS.stdBasis i) ((awayPairs i).image edgeState) := by decide

theorem singleton_not_away_image : ∀ i : Fin 6,
    SS.stdBasis i ∉ (awayPairs i).image edgeState := by decide

theorem wt_single_row : ∀ i j : Fin 6,
    (⟨SS.stdBasis i, SS.stdBasis j⟩ : SS.PauliString 6).wt ≤ 2 := by decide

theorem edge_bdot : ∀ (i j : Fin 6) (ij : Fin 6 × Fin 6),
    ij ∈ awayPairs i →
    SS.bdot (SS.stdBasis j) (edgeState ij) = !(touches ij j) := by decide

lemma offSum_single_expand (c d : SS.BitString 6 → ℂ)
    (i : Fin 6) (z : SS.BitString 6) :
    offSumOn S0 S1 c d (SS.stdBasis i) z =
      signMul (SS.bdot z (SS.stdBasis i))
        (star (c zero6) * u d i) +
      ∑ ij ∈ awayPairs i,
        signMul (SS.bdot z (edgeState ij))
          (star (c (topRecip i ij)) * v d ij.1 ij.2) := by
  unfold offSumOn
  rw [single_flip_intersection i]
  rw [Finset.sum_insert (singleton_not_away_image i)]
  rw [Finset.sum_image]
  · rw [SS.bxor_self]
    rfl
  · apply edgeState_injective_on.mono
    intro ij hij
    change ij ∈ awayPairs i at hij
    exact (Finset.filter_subset _ _) hij

lemma star_signMul (b : Bool) (z : ℂ) :
    star (signMul b z) = signMul b (star z) := by
  cases b <;> simp [signMul]

/-- The five star equations obtained by exact two-row Walsh inversion. -/
theorem star_equation (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (i j : Fin 6) (hij : i ≠ j) :
    (∑ ij ∈ awayPairs i,
      if touches ij j = true then
        star (v d ij.1 ij.2) * c (topRecip i ij) else 0) = 0 := by
  have hcS := full_support0 hc
  have hdS := full_support1 hd
  have h0 := offSumOn_eq_zero_of_hasDistance S0 S1 c d hcS hdS hcode
    (SS.stdBasis i) zero6 (wt_singleton_zero i)
  have hj := offSumOn_eq_zero_of_hasDistance S0 S1 c d hcS hdS hcode
    (SS.stdBasis i) (SS.stdBasis j) (wt_single_row i j)
  rw [offSum_single_expand] at h0 hj
  have hvac := vacuum_singleton_product c d hc hd hcode i
  change star (c zero6) * u d i = 0 at hvac
  change signMul (SS.bdot zero6 (SS.stdBasis i))
      (star (c zero6) * u d i) + _ = 0 at h0
  rw [bdot_zero6, signMul_false, hvac, zero_add] at h0
  rw [Finset.sum_congr rfl (fun ij hmem => by
    rw [bdot_zero6, signMul_false])] at h0
  have hji : SS.bdot (SS.stdBasis j) (SS.stdBasis i) = false := by
    rw [bdot_stdBasis]
    simp [SS.stdBasis, Ne.symm hij]
  change signMul (SS.bdot (SS.stdBasis j) (SS.stdBasis i))
      (star (c zero6) * u d i) + _ = 0 at hj
  rw [hji, signMul_false, hvac, zero_add] at hj
  have hrewrite : ∀ ij ∈ awayPairs i,
      SS.bdot (SS.stdBasis j) (edgeState ij) =
        !(touches ij j) := edge_bdot i j
  rw [Finset.sum_congr rfl (fun ij hmem => by rw [hrewrite ij hmem])] at hj
  have h0s : (∑ ij ∈ awayPairs i,
      star (v d ij.1 ij.2) * c (topRecip i ij)) = 0 := by
    calc
      _ = star (∑ ij ∈ awayPairs i,
          star (c (topRecip i ij)) * v d ij.1 ij.2) := by
        rw [star_sum]
        refine Finset.sum_congr rfl (fun ij hmem => ?_)
        rw [star_mul', star_star]
        exact mul_comm _ _
      _ = star 0 := congrArg star h0
      _ = 0 := by simp
  have hjs : (∑ ij ∈ awayPairs i,
      signMul (!(touches ij j))
        (star (v d ij.1 ij.2) * c (topRecip i ij))) = 0 := by
    calc
      _ = star (∑ ij ∈ awayPairs i,
          signMul (!(touches ij j))
            (star (c (topRecip i ij)) * v d ij.1 ij.2)) := by
        rw [star_sum]
        refine Finset.sum_congr rfl (fun ij hmem => ?_)
        rw [star_signMul, star_mul', star_star]
        exact congrArg (signMul (!(touches ij j))) (mul_comm _ _)
      _ = star 0 := congrArg star hj
      _ = 0 := by simp
  have hcomb :
      (∑ ij ∈ awayPairs i,
        if touches ij j = true then
          star (v d ij.1 ij.2) * c (topRecip i ij) else 0) =
        ((∑ ij ∈ awayPairs i,
            star (v d ij.1 ij.2) * c (topRecip i ij)) +
          ∑ ij ∈ awayPairs i,
            signMul (!(touches ij j))
              (star (v d ij.1 ij.2) * c (topRecip i ij))) / 2 := by
    calc
      _ = ∑ ij ∈ awayPairs i,
          (star (v d ij.1 ij.2) * c (topRecip i ij) +
            signMul (!(touches ij j))
              (star (v d ij.1 ij.2) * c (topRecip i ij))) / 2 := by
        refine Finset.sum_congr rfl (fun ij hmem => ?_)
        cases ht : touches ij j <;> simp [signMul]
      _ = _ := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
  rw [hcomb, h0s, hjs]
  norm_num

end

end SixQubit.Orbit8Universal
