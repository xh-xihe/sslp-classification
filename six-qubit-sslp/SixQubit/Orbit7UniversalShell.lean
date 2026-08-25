import SixQubit.CodeBridge

/-!
# Orbit 7 universal converse, I: active-shell rigidity

We work first in the uniform gauge `(0,1,1,1,1,1)`.  Coordinate zero is
the zero-angle qubit and the other five coordinates are active.  The two
logical states occupy active Hamming residues zero and two modulo three.

For completely arbitrary normalized states on those full fibers, genuine
distance three implies equality of every one- and two-coordinate occupation
moment.  Summing the active rows gives the first two active Hamming moments
and pins the four shell masses to

```
    logical zero:  mass(active weight 0) = 1/6,
                   mass(active weight 3) = 5/6;
    logical one:   mass(active weight 2) = 5/6,
                   mass(active weight 5) = 1/6.
```

No support pattern inside a shell is assumed.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators
open SixQubit

noncomputable section

def uniformAv : Fin 6 -> ZMod 3 := ![0,1,1,1,1,1]

def S0 : Finset (SS.BitString 6) :=
  Finset.univ.filter (fun x => SS.weight uniformAv x = 0)

def S2 : Finset (SS.BitString 6) :=
  Finset.univ.filter (fun x => SS.weight uniformAv x = 2)

/-- Hamming weight on the five active coordinates `1,...,5`. -/
def activeWt (x : SS.BitString 6) : Nat :=
  ∑ i : Fin 5, if x i.succ = true then 1 else 0

def shellMass (S : Finset (SS.BitString 6)) (c : SS.BitString 6 -> ℂ)
    (w : Nat) : ℝ :=
  ∑ x ∈ S.filter (fun x => activeWt x = w), Complex.normSq (c x)

def firstMoment (S : Finset (SS.BitString 6)) (c : SS.BitString 6 -> ℂ) : ℝ :=
  ∑ x ∈ S, (activeWt x : ℝ) * Complex.normSq (c x)

def secondMoment (S : Finset (SS.BitString 6)) (c : SS.BitString 6 -> ℂ) : ℝ :=
  ∑ x ∈ S, (activeWt x : ℝ)^2 * Complex.normSq (c x)

theorem S0_shells : ∀ x ∈ S0, activeWt x = 0 ∨ activeWt x = 3 := by decide
theorem S2_shells : ∀ x ∈ S2, activeWt x = 2 ∨ activeWt x = 5 := by decide

lemma sum_active_indicators (x : SS.BitString 6) (a : ℝ) :
    ∑ i : Fin 5, (if x i.succ = true then a else 0) = (activeWt x : ℝ) * a := by
  rw [← Finset.sum_filter]
  simp [activeWt, Finset.sum_const, nsmul_eq_mul]

lemma sum_active_pair_indicators (x : SS.BitString 6) (a : ℝ) :
    ∑ i : Fin 5, ∑ j : Fin 5,
      (if x i.succ = true ∧ x j.succ = true then a else 0) =
        (activeWt x : ℝ)^2 * a := by
  have hinner : ∀ i : Fin 5,
      (∑ j : Fin 5, if x i.succ = true ∧ x j.succ = true then a else 0) =
        if x i.succ = true then (activeWt x : ℝ) * a else 0 := by
    intro i
    by_cases hi : x i.succ = true
    · simp only [hi, true_and]
      exact sum_active_indicators x a
    · simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [sum_active_indicators]
  ring

lemma sum_active_occ_eq_first
    (S : Finset (SS.BitString 6)) (c : SS.BitString 6 -> ℂ) :
    ∑ i : Fin 5, occOn S c i.succ = firstMoment S c := by
  classical
  unfold occOn firstMoment
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  simpa using sum_active_indicators x (Complex.normSq (c x))

lemma sum_active_occ2_eq_second
    (S : Finset (SS.BitString 6)) (c : SS.BitString 6 -> ℂ) :
    ∑ i : Fin 5, ∑ j : Fin 5, occ2On S c i.succ j.succ = secondMoment S c := by
  classical
  unfold occ2On secondMoment
  simp_rw [Finset.sum_filter]
  calc
    (∑ i : Fin 5, ∑ j : Fin 5, ∑ x ∈ S,
        if x i.succ = true ∧ x j.succ = true then Complex.normSq (c x) else 0) =
      ∑ i : Fin 5, ∑ x ∈ S, ∑ j : Fin 5,
        if x i.succ = true ∧ x j.succ = true then Complex.normSq (c x) else 0 := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
    _ = ∑ x ∈ S, ∑ i : Fin 5, ∑ j : Fin 5,
        if x i.succ = true ∧ x j.succ = true then Complex.normSq (c x) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ x ∈ S, (activeWt x : ℝ)^2 * Complex.normSq (c x) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      simpa using sum_active_pair_indicators x (Complex.normSq (c x))

lemma mass_S0 (c : SS.BitString 6 -> ℂ) :
    massOn S0 c = shellMass S0 c 0 + shellMass S0 c 3 := by
  classical
  unfold massOn shellMass
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S0_shells x hx with h | h <;> simp [h]

lemma mass_S2 (d : SS.BitString 6 -> ℂ) :
    massOn S2 d = shellMass S2 d 2 + shellMass S2 d 5 := by
  classical
  unfold massOn shellMass
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S2_shells x hx with h | h <;> simp [h]

lemma first_S0 (c : SS.BitString 6 -> ℂ) :
    firstMoment S0 c = 3*shellMass S0 c 3 := by
  classical
  unfold firstMoment shellMass
  simp_rw [Finset.sum_filter]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S0_shells x hx with h | h <;> simp [h]

lemma first_S2 (d : SS.BitString 6 -> ℂ) :
    firstMoment S2 d = 2*shellMass S2 d 2 + 5*shellMass S2 d 5 := by
  classical
  unfold firstMoment shellMass
  simp_rw [Finset.sum_filter]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S2_shells x hx with h | h <;> simp [h]

lemma second_S0 (c : SS.BitString 6 -> ℂ) :
    secondMoment S0 c = 9*shellMass S0 c 3 := by
  classical
  unfold secondMoment shellMass
  simp_rw [Finset.sum_filter]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S0_shells x hx with h | h
  · simp [h]
  · simp only [h]
    norm_num

lemma second_S2 (d : SS.BitString 6 -> ℂ) :
    secondMoment S2 d = 4*shellMass S2 d 2 + 25*shellMass S2 d 5 := by
  classical
  unfold secondMoment shellMass
  simp_rw [Finset.sum_filter]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rcases S2_shells x hx with h | h <;> simp [h] <;> norm_num

theorem full_support0 {c : SS.BitString 6 -> ℂ}
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0) :
    ∀ x, x ∉ S0 -> c x = 0 := by
  intro x hx
  apply hc x
  simpa [S0] using hx

theorem full_support2 {d : SS.BitString 6 -> ℂ}
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0) :
    ∀ x, x ∉ S2 -> d x = 0 := by
  intro x hx
  apply hd x
  simpa [S2] using hx

/-- Shell rigidity for an arbitrary exact orbit-7 code in the uniform gauge. -/
theorem rigid_shells (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    shellMass S0 c 0 = 1/6 ∧ shellMass S0 c 3 = 5/6 ∧
      shellMass S2 d 2 = 5/6 ∧ shellMass S2 d 5 = 1/6 := by
  have hcS := full_support0 hc
  have hdS := full_support2 hd
  have n0 := massOn_eq_one S0 c hcS hnc
  have n2 := massOn_eq_one S2 d hdS hnd
  rw [mass_S0] at n0
  rw [mass_S2] at n2
  have hocc : ∀ i, occOn S0 c i = occOn S2 d i :=
    occOn_eq_of_hasDistance S0 S2 c d hcS hdS hnc hnd hcode
  have hocc2 : ∀ i j, occ2On S0 c i j = occ2On S2 d i j :=
    occ2On_eq_of_hasDistance S0 S2 c d hcS hdS hnc hnd hcode
  have e1 : firstMoment S0 c = firstMoment S2 d := by
    rw [← sum_active_occ_eq_first, ← sum_active_occ_eq_first]
    exact Finset.sum_congr rfl (fun i _ => hocc i.succ)
  have e2 : secondMoment S0 c = secondMoment S2 d := by
    rw [← sum_active_occ2_eq_second, ← sum_active_occ2_eq_second]
    exact Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ => hocc2 i.succ j.succ))
  rw [first_S0, first_S2] at e1
  rw [second_S0, second_S2] at e2
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end

end SixQubit.Orbit7Universal
