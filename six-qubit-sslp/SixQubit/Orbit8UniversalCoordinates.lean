import SixQubit.Orbit8UniversalVacuum

/-!
# Orbit 8 universal converse, III: coordinate cross equations

After vacuum elimination the two words live on shells `3,6` and `1,4`.
This file names the singleton, complementary-pair, triple, and all-one
coordinates and extracts the weight-two cross-KL equations directly from
`HasDistance`.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

noncomputable section

def ones6 : SS.BitString 6 := fun _ => true

def pairMask (i j : Fin 6) : SS.BitString 6 :=
  SS.bxor (SS.stdBasis i) (SS.stdBasis j)

def tripleMask (i j k : Fin 6) : SS.BitString 6 :=
  SS.bxor (pairMask i j) (SS.stdBasis k)

def u (d : SS.BitString 6 → ℂ) (i : Fin 6) : ℂ := d (SS.stdBasis i)

def v (d : SS.BitString 6 → ℂ) (i j : Fin 6) : ℂ :=
  d (SS.complement (pairMask i j))

def a (c : SS.BitString 6 → ℂ) (i j k : Fin 6) : ℂ :=
  c (tripleMask i j k)

def ball (c : SS.BitString 6 → ℂ) : ℂ := c ones6

theorem wt_pair_zero : ∀ i j : Fin 6,
    (⟨pairMask i j, zero6⟩ : SS.PauliString 6).wt ≤ 2 := by decide

theorem stdBasis_injective : Function.Injective (@SS.stdBasis 6) := by decide

theorem pair_flip_intersection : ∀ i j : Fin 6, i ≠ j →
    S1.filter (fun y => SS.bxor y (pairMask i j) ∈ S0) =
      insert (SS.complement (pairMask i j))
        ((Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j)).image SS.stdBasis) := by decide

theorem complement_pair_not_singleton_image : ∀ i j : Fin 6, i ≠ j →
    SS.complement (pairMask i j) ∉
      (Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j)).image SS.stdBasis := by decide

theorem complement_pair_xor : ∀ i j : Fin 6, i ≠ j →
    SS.bxor (SS.complement (pairMask i j)) (pairMask i j) = ones6 := by decide

lemma offSum_pair_expand (c d : SS.BitString 6 → ℂ) (i j : Fin 6) (hij : i ≠ j) :
    offSumOn S0 S1 c d (pairMask i j) zero6 =
      star (ball c) * v d i j +
        ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
          star (a c i j k) * u d k := by
  classical
  unfold offSumOn
  rw [pair_flip_intersection i j hij]
  rw [Finset.sum_insert (complement_pair_not_singleton_image i j hij)]
  rw [Finset.sum_image (fun x hx y hy hxy => stdBasis_injective hxy)]
  rw [bdot_zero6, signMul_false, complement_pair_xor i j hij]
  unfold ball v a u tripleMask
  refine congrArg (star (c ones6) * d (SS.complement (pairMask i j)) + ·)
    (Finset.sum_congr rfl (fun k hk => ?_))
  rw [bdot_zero6, signMul_false, SS.bxor_comm]

/-- The pair-cross equations of the manuscript, derived from genuine KL. -/
theorem pair_cross (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (i j : Fin 6) (hij : i ≠ j) :
    star (ball c) * v d i j +
        ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
          star (a c i j k) * u d k = 0 := by
  have hcS := full_support0 hc
  have hdS := full_support1 hd
  have h := offSumOn_eq_zero_of_hasDistance S0 S1 c d hcS hdS hcode
    (pairMask i j) zero6 (wt_pair_zero i j)
  rwa [offSum_pair_expand c d i j hij] at h

def p (d : SS.BitString 6 → ℂ) (i : Fin 6) : ℝ := Complex.normSq (u d i)

def r (d : SS.BitString 6 → ℂ) : ℝ := ∑ i, p d i

lemma shellMass_S0_six (c : SS.BitString 6 → ℂ) :
    shellMass S0 c 6 = Complex.normSq (ball c) := by
  unfold shellMass
  rw [show S0.filter (fun x => SS.hammingWt x = 6) = {ones6} from by decide]
  simp [ball]

lemma shellMass_S1_one_eq_r (d : SS.BitString 6 → ℂ) :
    shellMass S1 d 1 = r d := by
  unfold shellMass r p u
  rw [show S1.filter (fun x => SS.hammingWt x = 1) =
      Finset.univ.image SS.stdBasis from by decide]
  rw [Finset.sum_image (fun x hx y hy hxy => stdBasis_injective hxy)]

theorem rigid_coordinate_norms (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    Complex.normSq (ball c) = 1/6 ∧ r d = 1/6 ∧ ball c ≠ 0 := by
  obtain ⟨hc0, hm0, hm3, hm6, hn1, hn4⟩ :=
    rigid_shells c d hc hd hnc hnd hcode
  rw [shellMass_S0_six] at hm6
  rw [shellMass_S1_one_eq_r] at hn1
  refine ⟨hm6, hn1, ?_⟩
  intro hb
  rw [hb] at hm6
  norm_num at hm6

end

end SixQubit.Orbit8Universal
