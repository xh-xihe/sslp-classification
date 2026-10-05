import MainTheory.GeneralSectorMoments
import MainTheory.PhaseSectorMoments

/-! Binary moments and diagonal Pauli characters on the same full fibers. -/
namespace MainTheory.DiagonalMomentBridge

open scoped BigOperators
noncomputable section
variable {n q : ℕ}

def bitValue (x : SS.BitString n) (j : Fin n) : ℝ := if x j then 1 else 0

def zValue (x : SS.BitString n) (j : Fin n) : ℝ := 1 - 2 * bitValue x j

def moment (p : SS.BitString n → ℝ) (f : SS.BitString n → Fin n → ℝ)
    (J : Finset (Fin n)) : ℝ := ∑ x, p x * ∏ j ∈ J, f x j

theorem affine_expansion (f : Fin n → ℝ) (J : Finset (Fin n)) (a b : ℝ) :
    (∏ j ∈ J, (a + b * f j)) =
      ∑ S ∈ J.powerset, (b ^ S.card * (∏ j ∈ S, f j)) * a ^ (J.card - S.card) := by
  simp_rw [add_comm a]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hS)]

theorem matching_affine_moments (p r : SS.BitString n → ℝ)
    (f : SS.BitString n → Fin n → ℝ) (d : ℕ)
    (h : ∀ J : Finset (Fin n), J.card < d → moment p f J = moment r f J)
    (a b : ℝ) (J : Finset (Fin n)) (hJ : J.card < d) :
    moment p (fun x j => a + b * f x j) J =
      moment r (fun x j => a + b * f x j) J := by
  unfold moment
  simp_rw [affine_expansion, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hs : S.card < d := lt_of_le_of_lt
    (Finset.card_le_card (Finset.mem_powerset.mp hS)) hJ
  have he := h S hs
  unfold moment at he
  calc
    _ = (b ^ S.card * a ^ (J.card - S.card)) *
        (∑ x, p x * ∏ j ∈ S, f x j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    _ = (b ^ S.card * a ^ (J.card - S.card)) *
        (∑ x, r x * ∏ j ∈ S, f x j) := by rw [he]
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring

theorem binary_iff_character_moments (p r : SS.BitString n → ℝ) (d : ℕ) :
    (∀ J : Finset (Fin n), J.card < d → moment p bitValue J = moment r bitValue J) ↔
      (∀ J : Finset (Fin n), J.card < d → moment p zValue J = moment r zValue J) := by
  constructor
  · intro h J hJ
    simpa only [zValue, sub_eq_add_neg, neg_mul] using
      matching_affine_moments p r bitValue d h 1 (-2) J hJ
  · intro h J hJ
    have he := matching_affine_moments p r zValue d h (1 / 2) (-1 / 2) J hJ
    have hf : (fun (x : SS.BitString n) (j : Fin n) =>
        (1 : ℝ) / 2 + (-1 / 2) * zValue x j) = bitValue := by
      funext x j
      unfold zValue
      ring
    rwa [hf] at he

def mask (J : Finset (Fin n)) : SS.BitString n := fun j => decide (j ∈ J)

theorem character_eq_product (J : Finset (Fin n)) (x : SS.BitString n) :
    SS.MacWilliams.chi (mask J) x = ∏ j ∈ J, zValue x j := by
  unfold SS.MacWilliams.chi
  have h (j : Fin n) :
      (if mask J j && x j then (-1 : ℝ) else 1) =
        (if j ∈ J then zValue x j else 1) := by
    by_cases hj : j ∈ J <;> cases hx : x j <;> norm_num [mask, zValue, bitValue, hj, hx]
  simp_rw [h]
  symm
  calc
    (∏ j ∈ J, zValue x j) = ∏ j ∈ J, (if j ∈ J then zValue x j else 1) :=
      Finset.prod_congr rfl fun j hj => by rw [if_pos hj]
    _ = _ := Finset.prod_subset (Finset.subset_univ J) fun j _ hj => by rw [if_neg hj]

theorem diagonal_action (J : Finset (Fin n)) (v : SS.State n ℂ) (x : SS.BitString n) :
    SS.pauliAct (⟨fun _ => false, mask J⟩ : SS.PauliString n) v x =
      ((∏ j ∈ J, zValue x j : ℝ) : ℂ) * v x := by
  have hn : (⟨fun _ => false, mask J⟩ : SS.PauliString n).numY = 0 := by
    simp [SS.PauliString.numY]
  simp only [SS.pauliAct, hn, pow_zero, one_mul, SS.bxor_zero]
  rw [SS.MacWilliams.signC_bdot, character_eq_product]

theorem fiber_probability_sum (a : Fin n → ZMod q) (b : ZMod q)
    (v : SS.State n ℂ) (hv : SS.SSConditionState a b v) (hn : SS.innerC v v = 1) :
    ∑ x ∈ Finset.univ.filter (fun x => SS.weight a x = b), Complex.normSq (v x) = 1 := by
  apply SixQubit.massOn_eq_one _ v _ hn
  intro x hx
  by_contra h
  exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hv x h⟩)

end
end MainTheory.DiagonalMomentBridge
