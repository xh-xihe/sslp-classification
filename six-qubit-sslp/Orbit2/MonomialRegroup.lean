import Orbit2.MonomialIndex
import Orbit2.BlockRegroup

namespace Orbit2.Quartic
open scoped BigOperators

theorem orders_monomial_product (t : Fin 32 → ℂ) (r : Fin 528) (p : Fin 32 × Fin 32)
    (hp : p ∈ orders r) : t p.1 * t p.2 = quadraticMonomials t r := by
  unfold orders at hp
  dsimp only at hp
  split_ifs at hp
  · simp only [List.mem_singleton] at hp
    rw [hp]
    rfl
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp|hp
    · rw [hp]; rfl
    · rw [hp]; exact mul_comm _ _

theorem orders_fiber (r : Fin 528) :
    (Finset.univ.filter fun p : Fin 32 × Fin 32 => pairIndex p=r) = (orders r).toFinset := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,List.mem_toFinset]
  constructor
  · intro h
    rw [← h]
    exact pairIndex_mem p
  · intro hp
    have h := (List.all_eq_true.mp (orders_pairIndex r)) p hp
    exact of_decide_eq_true h

theorem sum_ordered_pairs (f : Fin 32 × Fin 32 → ℂ) :
    (∑ p, f p) = ∑ r : Fin 528, ((orders r).map f).sum := by
  rw [← Finset.sum_fiberwise Finset.univ pairIndex f]
  apply Finset.sum_congr rfl
  intro r _
  rw [orders_fiber,List.sum_toFinset f (orders_nodup r)]


theorem sum_ordered_pairs_finset (f : Fin 32 × Fin 32 → ℂ) :
    (∑ p, f p) = ∑ r : Fin 528, ∑ p ∈ (orders r).toFinset, f p := by
  rw [← Finset.sum_fiberwise Finset.univ pairIndex f]
  simp_rw [orders_fiber]

theorem twiceCoefficient_eq_sum (r c : Fin 528) :
    twiceCoefficient r c = ∑ uv ∈ (orders r).toFinset, ∑ xy ∈ (orders c).toFinset,
      gatedCoefficient uv.1 uv.2 xy.1 xy.2 := by
  unfold twiceCoefficient
  rw [← List.sum_toFinset _ (orders_nodup r)]
  apply Finset.sum_congr rfl
  intro uv _
  exact (List.sum_toFinset _ (orders_nodup c)).symm

theorem monomial_factor (t : Fin 32 → ℂ) (r c : Fin 528) (uv xy : Fin 32 × Fin 32)
    (huv : uv ∈ orders r) (hxy : xy ∈ orders c) :
    star (t uv.1) * t xy.1 * star (t uv.2) * t xy.2 =
      star (quadraticMonomials t r) * quadraticMonomials t c := by
  rw [← orders_monomial_product t r uv huv,← orders_monomial_product t c xy hxy,star_mul]
  ring

theorem orderedPolynomial_eq_fullEnergy (t : Fin 32 → ℂ) :
    orderedPolynomial rawCoefficient t = fullCoefficientEnergy (quadraticMonomials t) := by
  have hp : orderedPolynomial rawCoefficient t =
      ∑ uv : Fin 32 × Fin 32, ∑ xy : Fin 32 × Fin 32,
        star (t uv.1) * t xy.1 * star (t uv.2) * t xy.2 *
          (rawCoefficient uv.1 uv.2 xy.1 xy.2 : ℂ) := by
    simp only [orderedPolynomial,Fintype.sum_prod_type]
    calc
      _ = ∑ u, ∑ y, ∑ v, ∑ x, star (t u) * t x * star (t v) * t y *
          (rawCoefficient u v x y : ℂ) := (sum_rotate_four _).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_comm]
  rw [hp,sum_ordered_pairs_finset]
  simp_rw [sum_ordered_pairs_finset]
  unfold fullCoefficientEnergy
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [twiceCoefficient_eq_sum]
  simp only [Int.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro xy hxy
  rw [gatedCoefficient_eq_raw,monomial_factor t r c uv xy (List.mem_toFinset.mp huv) (List.mem_toFinset.mp hxy)]
end Orbit2.Quartic
