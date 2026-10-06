import SixQubit.CodeBridge
import SixQubit.Orbit8FamilyImage

/-!
# Orbit 8 universal converse, I: shell rigidity

This file begins the orbit-wide direction.  It is independent of the explicit
attainment family: `c,d` are arbitrary normalized states on the two complete
orbit-8 fibers and the only code hypothesis is genuine `HasDistance`.

The result here is the manuscript's shell normal form.  The later anti-linear
ladder and singleton-support argument are kept in a separate layer.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators
open SixQubit

noncomputable section

def av : Fin 6 → ZMod 3 := SixQubit.Orbit8Real.av

def S0 : Finset (SS.BitString 6) :=
  Finset.univ.filter (fun x => SS.weight av x = 0)

def S1 : Finset (SS.BitString 6) :=
  Finset.univ.filter (fun x => SS.weight av x = 1)

def shellMass (S : Finset (SS.BitString 6)) (c : SS.BitString 6 → ℂ)
    (w : Nat) : ℝ :=
  ∑ x ∈ S.filter (fun x => SS.hammingWt x = w), Complex.normSq (c x)

def firstMoment (S : Finset (SS.BitString 6)) (c : SS.BitString 6 → ℂ) : ℝ :=
  ∑ x ∈ S, (SS.hammingWt x : ℝ) * Complex.normSq (c x)

def secondMoment (S : Finset (SS.BitString 6)) (c : SS.BitString 6 → ℂ) : ℝ :=
  ∑ x ∈ S, (SS.hammingWt x : ℝ)^2 * Complex.normSq (c x)

theorem S0_shells : ∀ x ∈ S0,
    SS.hammingWt x = 0 ∨ SS.hammingWt x = 3 ∨ SS.hammingWt x = 6 := by decide

theorem S1_shells : ∀ x ∈ S1,
    SS.hammingWt x = 1 ∨ SS.hammingWt x = 4 := by decide

lemma sum_indicators (x : SS.BitString 6) (a : ℝ) :
    ∑ i : Fin 6, (if x i = true then a else 0) = (SS.hammingWt x : ℝ) * a := by
  rw [← Finset.sum_filter]
  simp [SS.hammingWt, Finset.sum_const, nsmul_eq_mul]

lemma sum_pair_indicators (x : SS.BitString 6) (a : ℝ) :
    ∑ i : Fin 6, ∑ j : Fin 6, (if x i = true ∧ x j = true then a else 0) =
      (SS.hammingWt x : ℝ)^2 * a := by
  have hinner : ∀ i : Fin 6,
      (∑ j : Fin 6, if x i = true ∧ x j = true then a else 0) =
        if x i = true then (SS.hammingWt x : ℝ) * a else 0 := by
    intro i
    by_cases hi : x i = true
    · simp only [hi, true_and]
      exact sum_indicators x a
    · simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [sum_indicators]
  ring

lemma sum_occ_eq_first (S : Finset (SS.BitString 6)) (c : SS.BitString 6 → ℂ) :
    ∑ i : Fin 6, occOn S c i = firstMoment S c := by
  classical
  unfold occOn firstMoment
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  simpa using sum_indicators x (Complex.normSq (c x))

lemma sum_occ2_eq_second (S : Finset (SS.BitString 6)) (c : SS.BitString 6 → ℂ) :
    ∑ i : Fin 6, ∑ j : Fin 6, occ2On S c i j = secondMoment S c := by
  classical
  unfold occ2On secondMoment
  simp_rw [Finset.sum_filter]
  calc
    (∑ i : Fin 6, ∑ j : Fin 6, ∑ x ∈ S,
        if x i = true ∧ x j = true then Complex.normSq (c x) else 0) =
      ∑ i : Fin 6, ∑ x ∈ S, ∑ j : Fin 6,
        if x i = true ∧ x j = true then Complex.normSq (c x) else 0 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
    _ = ∑ x ∈ S, ∑ i : Fin 6, ∑ j : Fin 6,
        if x i = true ∧ x j = true then Complex.normSq (c x) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ S, (SS.hammingWt x : ℝ)^2 * Complex.normSq (c x) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      simpa using sum_pair_indicators x (Complex.normSq (c x))

lemma mass_S0 (c : SS.BitString 6 → ℂ) :
    massOn S0 c = shellMass S0 c 0 + shellMass S0 c 3 + shellMass S0 c 6 := by
  classical
  unfold massOn shellMass
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S0_shells x hx with h | h | h <;> simp [h]

lemma mass_S1 (d : SS.BitString 6 → ℂ) :
    massOn S1 d = shellMass S1 d 1 + shellMass S1 d 4 := by
  classical
  unfold massOn shellMass
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S1_shells x hx with h | h <;> simp [h]

lemma first_S0 (c : SS.BitString 6 → ℂ) :
    firstMoment S0 c = 3*shellMass S0 c 3 + 6*shellMass S0 c 6 := by
  classical
  unfold firstMoment shellMass
  simp_rw [Finset.sum_filter]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S0_shells x hx with h | h | h <;> simp [h]

lemma first_S1 (d : SS.BitString 6 → ℂ) :
    firstMoment S1 d = shellMass S1 d 1 + 4*shellMass S1 d 4 := by
  classical
  unfold firstMoment shellMass
  simp_rw [Finset.sum_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S1_shells x hx with h | h <;> simp [h]

lemma second_S0 (c : SS.BitString 6 → ℂ) :
    secondMoment S0 c = 9*shellMass S0 c 3 + 36*shellMass S0 c 6 := by
  classical
  unfold secondMoment shellMass
  simp_rw [Finset.sum_filter]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S0_shells x hx with h | h | h <;> simp [h] <;> norm_num

lemma second_S1 (d : SS.BitString 6 → ℂ) :
    secondMoment S1 d = shellMass S1 d 1 + 16*shellMass S1 d 4 := by
  classical
  unfold secondMoment shellMass
  simp_rw [Finset.sum_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S1_shells x hx with h | h
  · simp [h]
  · simp only [h]
    norm_num

theorem full_support0 {c : SS.BitString 6 → ℂ}
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0) : ∀ x, x ∉ S0 → c x = 0 := by
  intro x hx
  apply hc x
  simpa [S0] using hx

theorem full_support1 {d : SS.BitString 6 → ℂ}
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0) : ∀ x, x ∉ S1 → d x = 0 := by
  intro x hx
  apply hd x
  simpa [S1] using hx

/-- The three shell masses on the bottom fiber and the two on the top fiber,
before the vacuum-elimination step. -/
theorem shell_parameter (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    let t := shellMass S1 d 4
    shellMass S1 d 1 = 1-t ∧
    shellMass S0 c 0 = 5/9-2*t/3 ∧
    shellMass S0 c 3 = 5/9+t/3 ∧
    shellMass S0 c 6 = (3*t-1)/9 := by
  have hcS := full_support0 hc
  have hdS := full_support1 hd
  have n0 := massOn_eq_one S0 c hcS hnc
  have n1 := massOn_eq_one S1 d hdS hnd
  rw [mass_S0] at n0
  rw [mass_S1] at n1
  have hocc : ∀ i, occOn S0 c i = occOn S1 d i :=
    occOn_eq_of_hasDistance S0 S1 c d hcS hdS hnc hnd hcode
  have hocc2 : ∀ i j, occ2On S0 c i j = occ2On S1 d i j :=
    occ2On_eq_of_hasDistance S0 S1 c d hcS hdS hnc hnd hcode
  have e1 : firstMoment S0 c = firstMoment S1 d := by
    rw [← sum_occ_eq_first, ← sum_occ_eq_first]
    exact Finset.sum_congr rfl (fun i _ => hocc i)
  have e2 : secondMoment S0 c = secondMoment S1 d := by
    rw [← sum_occ2_eq_second, ← sum_occ2_eq_second]
    exact Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => hocc2 i j))
  rw [first_S0, first_S1] at e1
  rw [second_S0, second_S1] at e2
  dsimp
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end

end SixQubit.Orbit8Universal
