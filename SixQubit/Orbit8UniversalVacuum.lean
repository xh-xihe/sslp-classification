import SixQubit.Orbit8UniversalShell

/-!
# Orbit 8 universal converse, II: elimination of the vacuum amplitude

The six off-diagonal rows with flip mask `e_i` are combined by a short Walsh
sum.  On the orbit-8 fibres the singleton `e_i` receives coefficient six,
whereas every weight-four word containing `i` receives coefficient zero.
Thus the genuine Knill--Laflamme equations imply
`conj(c_∅) d_{e_i}=0` for every `i`.  The shell equations then force the
vacuum amplitude to vanish and rigidify all five shell masses.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

noncomputable section

def zero6 : SS.BitString 6 := fun _ => false

def epsZ (b : Bool) : ℤ := if b then -1 else 1

@[simp] lemma epsZ_false : epsZ false = 1 := by rfl
@[simp] lemma epsZ_true : epsZ true = -1 := by rfl

lemma signMul_eq_epsZ (b : Bool) (u : ℂ) :
    signMul b u = (epsZ b : ℂ) * u := by
  cases b <;> simp [epsZ, signMul]

@[simp] lemma bdot_zero6 (y : SS.BitString 6) : SS.bdot zero6 y = false := by
  simp [zero6, SS.bdot]

/-- The only finite combinatorics used in the Walsh aggregate. -/
theorem singleton_walsh_coefficient :
    ∀ i : Fin 6, ∀ y : SS.BitString 6,
      y ∈ S1 → SS.bxor y (SS.stdBasis i) ∈ S0 →
      (1 + ∑ j ∈ (Finset.univ.erase i), epsZ (SS.bdot (SS.stdBasis j) y)) =
        if y = SS.stdBasis i then 6 else 0 := by decide

theorem singleton_mem_flip_intersection : ∀ i : Fin 6,
    SS.stdBasis i ∈ S1.filter (fun y => SS.bxor y (SS.stdBasis i) ∈ S0) := by decide

lemma offSum_walsh_aggregate (c d : SS.BitString 6 → ℂ) (i : Fin 6) :
    offSumOn S0 S1 c d (SS.stdBasis i) zero6 +
        ∑ j ∈ (Finset.univ.erase i),
          offSumOn S0 S1 c d (SS.stdBasis i) (SS.stdBasis j) =
      6 * (star (c zero6) * d (SS.stdBasis i)) := by
  classical
  unfold offSumOn
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ y ∈ S1.filter (fun y => SS.bxor y (SS.stdBasis i) ∈ S0),
        (signMul (SS.bdot zero6 y) (star (c (SS.bxor y (SS.stdBasis i))) * d y) +
          (∑ j ∈ Finset.univ.erase i,
            signMul (SS.bdot (SS.stdBasis j) y)
              (star (c (SS.bxor y (SS.stdBasis i))) * d y)))) =
      ∑ y ∈ S1.filter (fun y => SS.bxor y (SS.stdBasis i) ∈ S0),
        if y = SS.stdBasis i then
          6 * (star (c (SS.bxor y (SS.stdBasis i))) * d y) else 0 := by
        refine Finset.sum_congr rfl (fun y hy => ?_)
        have hy1 : y ∈ S1 := (Finset.mem_filter.mp hy).1
        have hy0 : SS.bxor y (SS.stdBasis i) ∈ S0 := (Finset.mem_filter.mp hy).2
        have hcoef := singleton_walsh_coefficient i y hy1 hy0
        rw [bdot_zero6, signMul_false]
        simp_rw [signMul_eq_epsZ]
        rw [← Finset.sum_mul]
        let u := star (c (SS.bxor y (SS.stdBasis i))) * d y
        change u + (∑ j ∈ Finset.univ.erase i,
          (epsZ (SS.bdot (SS.stdBasis j) y) : ℂ)) * u =
            if y = SS.stdBasis i then 6 * u else 0
        rw [show u + (∑ j ∈ Finset.univ.erase i,
              (epsZ (SS.bdot (SS.stdBasis j) y) : ℂ)) * u =
            ((1 : ℂ) + ∑ j ∈ Finset.univ.erase i,
              (epsZ (SS.bdot (SS.stdBasis j) y) : ℂ)) * u by ring]
        by_cases hyi : y = SS.stdBasis i
        · rw [if_pos hyi]
          rw [show (1 : ℂ) + ∑ j ∈ Finset.univ.erase i,
                (epsZ (SS.bdot (SS.stdBasis j) y) : ℂ) = 6 by
            exact_mod_cast (by simpa [hyi] using hcoef)]
        · rw [if_neg hyi]
          rw [show (1 : ℂ) + ∑ j ∈ Finset.univ.erase i,
                (epsZ (SS.bdot (SS.stdBasis j) y) : ℂ) = 0 by
            exact_mod_cast (by simpa [hyi] using hcoef)]
          simp
    _ = 6 * (star (c zero6) * d (SS.stdBasis i)) := by
      rw [Finset.sum_eq_single_of_mem (SS.stdBasis i)
        (singleton_mem_flip_intersection i)]
      · simp only [SS.bxor_self]
        change 6 * (star (c zero6) * d (SS.stdBasis i)) =
          6 * (star (c zero6) * d (SS.stdBasis i))
        rfl
      · intro b hb hbi
        simp [hbi]

theorem wt_singleton_zero : ∀ i : Fin 6,
    (⟨SS.stdBasis i, zero6⟩ : SS.PauliString 6).wt ≤ 2 := by decide

theorem wt_singleton_dressed : ∀ i j : Fin 6,
    (⟨SS.stdBasis i, SS.stdBasis j⟩ : SS.PauliString 6).wt ≤ 2 := by decide

/-- A direct consequence of the genuine code condition, with no phase or
amplitude assumptions: every singleton top coefficient is annihilated by the
vacuum bottom coefficient. -/
theorem vacuum_singleton_product (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    star (c zero6) * d (SS.stdBasis i) = 0 := by
  have hcS := full_support0 hc
  have hdS := full_support1 hd
  have h0 := offSumOn_eq_zero_of_hasDistance S0 S1 c d hcS hdS hcode
    (SS.stdBasis i) zero6 (wt_singleton_zero i)
  have hj : ∀ j : Fin 6,
      offSumOn S0 S1 c d (SS.stdBasis i) (SS.stdBasis j) = 0 := by
    intro j
    exact offSumOn_eq_zero_of_hasDistance S0 S1 c d hcS hdS hcode
      (SS.stdBasis i) (SS.stdBasis j) (wt_singleton_dressed i j)
  have hsum : ∑ j ∈ Finset.univ.erase i,
      offSumOn S0 S1 c d (SS.stdBasis i) (SS.stdBasis j) = 0 := by
    exact Finset.sum_eq_zero (fun j hjmem => hj j)
  have hagg := offSum_walsh_aggregate c d i
  rw [h0, hsum, add_zero] at hagg
  exact (mul_eq_zero.mp hagg.symm).resolve_left (by norm_num)

lemma shellMass_nonneg (S : Finset (SS.BitString 6))
    (f : SS.BitString 6 → ℂ) (w : Nat) : 0 ≤ shellMass S f w := by
  unfold shellMass
  exact Finset.sum_nonneg (fun x hx => Complex.normSq_nonneg (f x))

theorem hamming_one_is_stdBasis : ∀ x : SS.BitString 6,
    SS.hammingWt x = 1 → ∃ i : Fin 6, x = SS.stdBasis i := by decide

lemma shellMass_S0_zero (c : SS.BitString 6 → ℂ) :
    shellMass S0 c 0 = Complex.normSq (c zero6) := by
  unfold shellMass
  rw [show S0.filter (fun x => SS.hammingWt x = 0) = {zero6} from by decide]
  simp

lemma exists_nonzero_singleton_of_shellMass_pos (d : SS.BitString 6 → ℂ)
    (hpos : 0 < shellMass S1 d 1) :
    ∃ i : Fin 6, d (SS.stdBasis i) ≠ 0 := by
  unfold shellMass at hpos
  obtain ⟨x, hx, hxpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun y hy => Complex.normSq_nonneg (d y))).mp hpos
  have hw : SS.hammingWt x = 1 := (Finset.mem_filter.mp hx).2
  obtain ⟨i, rfl⟩ := hamming_one_is_stdBasis x hw
  refine ⟨i, ?_⟩
  intro hz
  simp [hz] at hxpos

/-- Vacuum elimination and all five rigid shell masses.  The assumptions are
only complete-fibre support, the two normalizations, and genuine distance
three; no individual KL row is assumed. -/
theorem rigid_shells (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    c zero6 = 0 ∧
    shellMass S0 c 0 = 0 ∧
    shellMass S0 c 3 = 5/6 ∧
    shellMass S0 c 6 = 1/6 ∧
    shellMass S1 d 1 = 1/6 ∧
    shellMass S1 d 4 = 5/6 := by
  have hs := shell_parameter c d hc hd hnc hnd hcode
  dsimp at hs
  let t : ℝ := shellMass S1 d 4
  have htdef : t = shellMass S1 d 4 := rfl
  have hnu1 : shellMass S1 d 1 = 1 - t := by simpa [t] using hs.1
  have hmu0 : shellMass S0 c 0 = 5/9 - 2*t/3 := by simpa [t] using hs.2.1
  have hmu3 : shellMass S0 c 3 = 5/9 + t/3 := by simpa [t] using hs.2.2.1
  have hmu6 : shellMass S0 c 6 = (3*t-1)/9 := by simpa [t] using hs.2.2.2
  have ht_le : t ≤ 5/6 := by
    have hnonneg := shellMass_nonneg S0 c 0
    linarith
  have hnu1_pos : 0 < shellMass S1 d 1 := by linarith
  obtain ⟨i, hdi⟩ := exists_nonzero_singleton_of_shellMass_pos d hnu1_pos
  have hvp := vacuum_singleton_product c d hc hd hcode i
  have hc0 : c zero6 = 0 := by
    have hstar : star (c zero6) = 0 :=
      (mul_eq_zero.mp hvp).resolve_right hdi
    exact star_eq_zero.mp hstar
  have hmass0 : shellMass S0 c 0 = 0 := by
    rw [shellMass_S0_zero, hc0]
    simp
  have ht : t = 5/6 := by linarith
  refine ⟨hc0, hmass0, ?_, ?_, ?_, ?_⟩ <;> linarith

end

end SixQubit.Orbit8Universal
