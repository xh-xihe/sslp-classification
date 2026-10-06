import MainTheory.SmithPairEmbedding

namespace MainTheory.SmithExistence

open scoped BigOperators

noncomputable section

variable {s : Type*} [DecidableEq s]

theorem prod_update_pair (d : s → ℕ) (S : Finset s) (i j : s)
    (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) (a b : ℕ) :
    (∏ k ∈ S, Function.update (Function.update d i a) j b k) =
      a * b * ∏ k ∈ (S.erase i).erase j, d k := by
  rw [Finset.prod_update_of_mem hj, Finset.sdiff_singleton_eq_erase,
    Finset.prod_update_of_mem (Finset.mem_erase.mpr ⟨hij, hi⟩),
    Finset.sdiff_singleton_eq_erase]
  have he : (S.erase j).erase i = (S.erase i).erase j := by ext k; simp; tauto
  rw [he]
  ring

theorem prod_pair (d : s → ℕ) (S : Finset s) (i j : s)
    (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) :
    (∏ k ∈ S, d k) = d i * d j * ∏ k ∈ (S.erase i).erase j, d k := by
  simpa only [Function.update_eq_self] using prod_update_pair d S i j hij hi hj (d i) (d j)

theorem gcdUpdate_pos (d : s → ℕ) (hd : ∀ k, 0 < d k) (i j k : s) :
    0 < gcdUpdate d i j k := by
  by_cases hkj : k = j
  · subst k
    simp only [gcdUpdate, Function.update_self]
    exact Nat.lcm_pos (hd i) (hd j)
  · by_cases hki : k = i
    · subst k
      simp only [gcdUpdate, Function.update_of_ne hkj, Function.update_self]
      exact Nat.gcd_pos_of_pos_left _ (hd i)
    · simpa only [gcdUpdate, Function.update_of_ne hkj, Function.update_of_ne hki] using hd k

variable [Fintype s] [LinearOrder s] [LocallyFiniteOrderBot s]

def prefixProduct (d : s → ℕ) (k : s) : ℕ := ∏ l ∈ Finset.Iic k, d l

def smithMeasure (d : s → ℕ) : ℕ := ∑ k, prefixProduct d k

omit [Fintype s] in
theorem prefixProduct_gcd_le (d : s → ℕ) (hd : ∀ k, 0 < d k)
    (i j : s) (hij : i < j) (k : s) :
    prefixProduct (gcdUpdate d i j) k ≤ prefixProduct d k := by
  have hij' : i ≠ j := ne_of_lt hij
  unfold prefixProduct gcdUpdate
  by_cases hjk : j ≤ k
  · have hi : i ∈ Finset.Iic k := Finset.mem_Iic.mpr (le_trans (le_of_lt hij) hjk)
    have hj : j ∈ Finset.Iic k := Finset.mem_Iic.mpr hjk
    rw [prod_update_pair d _ i j hij' hi hj,
      prod_pair d _ i j hij' hi hj, Nat.gcd_mul_lcm]
  · have hj : j ∉ Finset.Iic k := by simpa using hjk
    rw [Finset.prod_update_of_notMem hj]
    by_cases hik : i ≤ k
    · have hi : i ∈ Finset.Iic k := Finset.mem_Iic.mpr hik
      rw [Finset.prod_update_of_mem hi, Finset.sdiff_singleton_eq_erase,
        ← Finset.mul_prod_erase (Finset.Iic k) d hi]
      exact Nat.mul_le_mul_right _ (Nat.le_of_dvd (hd i) (Nat.gcd_dvd_left _ _))
    · rw [Finset.prod_update_of_notMem (by simpa using hik)]

omit [Fintype s] in
theorem prefixProduct_gcd_lt (d : s → ℕ) (hd : ∀ k, 0 < d k)
    (i j : s) (hij : i < j) (hnd : ¬ d i ∣ d j) :
    prefixProduct (gcdUpdate d i j) i < prefixProduct d i := by
  have hj : j ∉ Finset.Iic i := by simp [not_le_of_gt hij]
  have hi : i ∈ Finset.Iic i := by simp
  have hgle : Nat.gcd (d i) (d j) ≤ d i := Nat.le_of_dvd (hd i) (Nat.gcd_dvd_left _ _)
  have hgne : Nat.gcd (d i) (d j) ≠ d i := by
    intro he
    have hh := Nat.gcd_dvd_right (d i) (d j)
    rw [he] at hh
    exact hnd hh
  have hglt : Nat.gcd (d i) (d j) < d i := by omega
  unfold prefixProduct gcdUpdate
  rw [Finset.prod_update_of_notMem hj, Finset.prod_update_of_mem hi,
    Finset.sdiff_singleton_eq_erase, ← Finset.mul_prod_erase (Finset.Iic i) d hi]
  exact Nat.mul_lt_mul_of_pos_right hglt (Finset.prod_pos (fun k _ => hd k))

theorem smithMeasure_gcd_lt (d : s → ℕ) (hd : ∀ k, 0 < d k)
    (i j : s) (hij : i < j) (hnd : ¬ d i ∣ d j) :
    smithMeasure (gcdUpdate d i j) < smithMeasure d := by
  apply Finset.sum_lt_sum
  · intro k _
    exact prefixProduct_gcd_le d hd i j hij k
  · exact ⟨i, Finset.mem_univ _, prefixProduct_gcd_lt d hd i j hij hnd⟩

end

end MainTheory.SmithExistence
