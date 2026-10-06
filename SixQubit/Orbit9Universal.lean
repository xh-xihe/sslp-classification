import Mathlib

import SS.HilbertKL
import SixQubit.BEnumerator
import SixQubit.CodeBridge
import SixQubit.CodeEquiv
import SixQubit.CodeEquivEnum
import SixQubit.Orbit9Real
import SixQubit.Pin

/-!
# Orbit 9: universal support reduction (work in the uniform gauge)

This file proves statements about arbitrary amplitudes on the *complete*
orbit-9 fibres.  The sixth-qubit cube translation sends the original angle
vector `(1,1,1,1,1,2)` and fibres `(0,1)` to the uniform Hamming-residue
fibres `(1,2)` modulo three.  The definitions below describe those two full
21-point fibres; no displayed witness support is used.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate
open SS.MacWilliams

noncomputable section

def bs (b0 b1 b2 b3 b4 b5 : Bool) : SS.BitString 6 := ![b0,b1,b2,b3,b4,b5]

def e0 := bs true false false false false false
def e1 := bs false true false false false false
def e2 := bs false false true false false false
def e3 := bs false false false true false false
def e4 := bs false false false false true false
def e5 := bs false false false false false true

def one (i : Fin 6) : SS.BitString 6 := ![i=0, i=1, i=2, i=3, i=4, i=5]
def pair (i j : Fin 6) : SS.BitString 6 := SS.bxor (one i) (one j)

def S0 : Finset (SS.BitString 6) :=
  {one 0, one 1, one 2, one 3, one 4, one 5,
   SS.complement (pair 0 1), SS.complement (pair 0 2),
   SS.complement (pair 0 3), SS.complement (pair 0 4),
   SS.complement (pair 0 5), SS.complement (pair 1 2),
   SS.complement (pair 1 3), SS.complement (pair 1 4),
   SS.complement (pair 1 5), SS.complement (pair 2 3),
   SS.complement (pair 2 4), SS.complement (pair 2 5),
   SS.complement (pair 3 4), SS.complement (pair 3 5),
   SS.complement (pair 4 5)}

def S1 : Finset (SS.BitString 6) :=
  {pair 0 1, pair 0 2, pair 0 3, pair 0 4, pair 0 5,
   pair 1 2, pair 1 3, pair 1 4, pair 1 5, pair 2 3,
   pair 2 4, pair 2 5, pair 3 4, pair 3 5, pair 4 5,
   SS.complement (one 0), SS.complement (one 1),
   SS.complement (one 2), SS.complement (one 3),
   SS.complement (one 4), SS.complement (one 5)}

def uniformAv : Fin 6 → ZMod 3 := fun _ => 1

theorem S0_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight uniformAv x = 1) = S0 := by decide

theorem S1_eq_fiber :
    (Finset.univ : Finset (SS.BitString 6)).filter
      (fun x => SS.weight uniformAv x = 2) = S1 := by decide

lemma sum_S0 (f : SS.BitString 6 → ℝ) :
    (∑ x ∈ S0, f x) =
      f (one 0) + f (one 1) + f (one 2) + f (one 3) + f (one 4) + f (one 5) +
      f (SS.complement (pair 0 1)) + f (SS.complement (pair 0 2)) +
      f (SS.complement (pair 0 3)) + f (SS.complement (pair 0 4)) +
      f (SS.complement (pair 0 5)) + f (SS.complement (pair 1 2)) +
      f (SS.complement (pair 1 3)) + f (SS.complement (pair 1 4)) +
      f (SS.complement (pair 1 5)) + f (SS.complement (pair 2 3)) +
      f (SS.complement (pair 2 4)) + f (SS.complement (pair 2 5)) +
      f (SS.complement (pair 3 4)) + f (SS.complement (pair 3 5)) +
      f (SS.complement (pair 4 5)) := by
  unfold S0
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

lemma sum_S1 (f : SS.BitString 6 → ℝ) :
    (∑ x ∈ S1, f x) =
      f (pair 0 1) + f (pair 0 2) + f (pair 0 3) + f (pair 0 4) +
      f (pair 0 5) + f (pair 1 2) + f (pair 1 3) + f (pair 1 4) +
      f (pair 1 5) + f (pair 2 3) + f (pair 2 4) + f (pair 2 5) +
      f (pair 3 4) + f (pair 3 5) + f (pair 4 5) +
      f (SS.complement (one 0)) + f (SS.complement (one 1)) +
      f (SS.complement (one 2)) + f (SS.complement (one 3)) +
      f (SS.complement (one 4)) + f (SS.complement (one 5)) := by
  unfold S1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

def p (c : SS.State 6 ℂ) (i : Fin 6) : ℝ := Complex.normSq (c (one i))
def q (d : SS.State 6 ℂ) (i : Fin 6) : ℝ :=
  Complex.normSq (d (SS.complement (one i)))

def r (c : SS.State 6 ℂ) (i j : Fin 6) : ℝ :=
  if i = j then 0 else Complex.normSq (c (SS.complement (pair i j)))

def s (d : SS.State 6 ℂ) (i j : Fin 6) : ℝ :=
  if i = j then 0 else Complex.normSq (d (pair i j))

def Pmass (c : SS.State 6 ℂ) : ℝ := ∑ i, p c i
def Qmass (d : SS.State 6 ℂ) : ℝ := ∑ i, q d i
def Rdeg (c : SS.State 6 ℂ) (i : Fin 6) : ℝ := ∑ j, r c i j
def Sdeg (d : SS.State 6 ℂ) (i : Fin 6) : ℝ := ∑ j, s d i j
def Rmass (c : SS.State 6 ℂ) : ℝ := (1/2 : ℝ) * ∑ i, Rdeg c i
def Smass (d : SS.State 6 ℂ) : ℝ := (1/2 : ℝ) * ∑ i, Sdeg d i

lemma p_nonneg (c : SS.State 6 ℂ) (i : Fin 6) : 0 ≤ p c i :=
  Complex.normSq_nonneg _

lemma q_nonneg (d : SS.State 6 ℂ) (i : Fin 6) : 0 ≤ q d i :=
  Complex.normSq_nonneg _

lemma r_nonneg (c : SS.State 6 ℂ) (i j : Fin 6) : 0 ≤ r c i j := by
  unfold r
  split
  · norm_num
  · exact Complex.normSq_nonneg _

lemma s_nonneg (d : SS.State 6 ℂ) (i j : Fin 6) : 0 ≤ s d i j := by
  unfold s
  split
  · norm_num
  · exact Complex.normSq_nonneg _

lemma r_symm (c : SS.State 6 ℂ) (i j : Fin 6) : r c i j = r c j i := by
  unfold r pair
  by_cases h : i = j
  · simp [h]
  · have h' : j ≠ i := Ne.symm h
    simp [h, h', SS.bxor_comm]

lemma s_symm (d : SS.State 6 ℂ) (i j : Fin 6) : s d i j = s d j i := by
  unfold s pair
  by_cases h : i = j
  · simp [h]
  · have h' : j ≠ i := Ne.symm h
    simp [h, h', SS.bxor_comm]

set_option maxHeartbeats 2000000 in
lemma massOn_S0 (c : SS.State 6 ℂ) :
    SixQubit.massOn S0 c = Pmass c + Rmass c := by
  classical
  unfold SixQubit.massOn S0
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [Pmass, Rmass, Rdeg, p, r, one, pair, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 2000000 in
lemma massOn_S1 (d : SS.State 6 ℂ) :
    SixQubit.massOn S1 d = Smass d + Qmass d := by
  classical
  unfold SixQubit.massOn S1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp [Smass, Sdeg, Qmass, q, s, one, pair, Fin.sum_univ_succ]
  ring

/-! ## Aggregating the diagonal moment rows -/

def hwt (x : SS.BitString 6) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

@[simp] lemma hwt_one (i : Fin 6) : hwt (one i) = 1 := by
  revert i
  decide

@[simp] lemma hwt_pair (i j : Fin 6) (hij : i ≠ j) :
    hwt (pair i j) = 2 := by
  revert i j
  decide

@[simp] lemma hwt_complement_one (i : Fin 6) :
    hwt (SS.complement (one i)) = 5 := by
  revert i
  decide

@[simp] lemma hwt_complement_pair (i j : Fin 6) (hij : i ≠ j) :
    hwt (SS.complement (pair i j)) = 4 := by
  revert i j
  decide

@[simp] lemma choose_one_two : Nat.choose 1 2 = 0 := by decide
@[simp] lemma choose_two_two : Nat.choose 2 2 = 1 := by decide
@[simp] lemma choose_four_two : Nat.choose 4 2 = 6 := by decide
@[simp] lemma choose_five_two : Nat.choose 5 2 = 10 := by decide

lemma sum_occOn (S : Finset (SS.BitString 6)) (c : SS.State 6 ℂ) :
    (∑ i, SixQubit.occOn S c i) =
      ∑ x ∈ S, (hwt x : ℝ) * Complex.normSq (c x) := by
  classical
  unfold SixQubit.occOn
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [← Finset.sum_filter]
  simp [hwt, Finset.sum_const]

def pairIdx : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

def occ2Total (S : Finset (SS.BitString 6)) (c : SS.State 6 ℂ) : ℝ :=
  ∑ ij ∈ pairIdx, SixQubit.occ2On S c ij.1 ij.2

lemma pairIdx_count (x : SS.BitString 6) :
    (pairIdx.filter (fun ij => x ij.1 = true ∧ x ij.2 = true)).card =
      Nat.choose (hwt x) 2 := by
  revert x
  decide

lemma sum_occ2On (S : Finset (SS.BitString 6)) (c : SS.State 6 ℂ) :
    occ2Total S c =
      ∑ x ∈ S, ((Nat.choose (hwt x) 2 : ℕ) : ℝ) *
        Complex.normSq (c x) := by
  classical
  unfold occ2Total SixQubit.occ2On
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  simp [pairIdx_count]

set_option maxHeartbeats 2000000 in
lemma occTotal_S0 (c : SS.State 6 ℂ) :
    (∑ i, SixQubit.occOn S0 c i) = Pmass c + 4 * Rmass c := by
  rw [sum_occOn, sum_S0]
  simp [hwt_complement_pair]
  simp [Pmass, Rmass, Rdeg, p, r, one, pair, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 2000000 in
lemma occTotal_S1 (d : SS.State 6 ℂ) :
    (∑ i, SixQubit.occOn S1 d i) = 2 * Smass d + 5 * Qmass d := by
  rw [sum_occOn, sum_S1]
  simp [hwt_pair]
  simp [Smass, Sdeg, Qmass, q, s, one, pair, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 2000000 in
lemma occ2Total_S0 (c : SS.State 6 ℂ) :
    occ2Total S0 c = 6 * Rmass c := by
  rw [sum_occ2On, sum_S0]
  simp [hwt_complement_pair]
  simp [Rmass, Rdeg, r, one, pair, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 2000000 in
lemma occ2Total_S1 (d : SS.State 6 ℂ) :
    occ2Total S1 d = Smass d + 10 * Qmass d := by
  rw [sum_occ2On, sum_S1]
  simp [hwt_pair]
  simp [Smass, Sdeg, Qmass, q, s, one, pair, Fin.sum_univ_succ]
  ring

/-- The two diagonal KL layers (weight one and weight two), together with
normalization, rigidly determine the total mass in each Hamming shell. -/
theorem global_masses (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    Pmass c = 1/3 ∧ Rmass c = 2/3 ∧
      Smass d = 2/3 ∧ Qmass d = 1/3 := by
  have hm0 : Pmass c + Rmass c = 1 := by
    rw [← massOn_S0]
    exact SixQubit.massOn_eq_one S0 c hc hnc
  have hm1 : Smass d + Qmass d = 1 := by
    rw [← massOn_S1]
    exact SixQubit.massOn_eq_one S1 d hd hnd
  have ho : (∑ i, SixQubit.occOn S0 c i) =
      ∑ i, SixQubit.occOn S1 d i := by
    apply Finset.sum_congr rfl
    intro i _
    exact SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist i
  have ho2 : occ2Total S0 c = occ2Total S1 d := by
    unfold occ2Total
    apply Finset.sum_congr rfl
    intro ij _
    exact SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hdist
      ij.1 ij.2
  rw [occTotal_S0, occTotal_S1] at ho
  rw [occ2Total_S0, occ2Total_S1] at ho2
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

set_option maxHeartbeats 2000000 in
lemma Rmass_edges (c : SS.State 6 ℂ) :
    Rmass c =
      r c 0 1 + r c 0 2 + r c 0 3 + r c 0 4 + r c 0 5 +
      r c 1 2 + r c 1 3 + r c 1 4 + r c 1 5 +
      r c 2 3 + r c 2 4 + r c 2 5 +
      r c 3 4 + r c 3 5 + r c 4 5 := by
  simp [Rmass, Rdeg, Fin.sum_univ_succ, r, one, pair, SS.bxor_comm]
  ring

set_option maxHeartbeats 2000000 in
lemma Smass_edges (d : SS.State 6 ℂ) :
    Smass d =
      s d 0 1 + s d 0 2 + s d 0 3 + s d 0 4 + s d 0 5 +
      s d 1 2 + s d 1 3 + s d 1 4 + s d 1 5 +
      s d 2 3 + s d 2 4 + s d 2 5 +
      s d 3 4 + s d 3 5 + s d 4 5 := by
  simp [Smass, Sdeg, Fin.sum_univ_succ, s, one, pair, SS.bxor_comm]
  ring

set_option maxHeartbeats 4000000 in
lemma occOn_S0_formula (c : SS.State 6 ℂ) (i : Fin 6) :
    SixQubit.occOn S0 c i = p c i + Rmass c - Rdeg c i := by
  rw [Rmass_edges]
  unfold SixQubit.occOn
  fin_cases i
  all_goals first
  | change (∑ x ∈ S0.filter (fun x => x 0 = true), Complex.normSq (c x)) = _
    rw [show S0.filter (fun x => x 0 = true) =
        {one 0, SS.complement (pair 1 2), SS.complement (pair 1 3),
         SS.complement (pair 1 4), SS.complement (pair 1 5),
         SS.complement (pair 2 3), SS.complement (pair 2 4),
         SS.complement (pair 2 5), SS.complement (pair 3 4),
         SS.complement (pair 3 5), SS.complement (pair 4 5)} from by decide]
  | change (∑ x ∈ S0.filter (fun x => x 1 = true), Complex.normSq (c x)) = _
    rw [show S0.filter (fun x => x 1 = true) =
        {one 1, SS.complement (pair 0 2), SS.complement (pair 0 3),
         SS.complement (pair 0 4), SS.complement (pair 0 5),
         SS.complement (pair 2 3), SS.complement (pair 2 4),
         SS.complement (pair 2 5), SS.complement (pair 3 4),
         SS.complement (pair 3 5), SS.complement (pair 4 5)} from by decide]
  | change (∑ x ∈ S0.filter (fun x => x 2 = true), Complex.normSq (c x)) = _
    rw [show S0.filter (fun x => x 2 = true) =
        {one 2, SS.complement (pair 0 1), SS.complement (pair 0 3),
         SS.complement (pair 0 4), SS.complement (pair 0 5),
         SS.complement (pair 1 3), SS.complement (pair 1 4),
         SS.complement (pair 1 5), SS.complement (pair 3 4),
         SS.complement (pair 3 5), SS.complement (pair 4 5)} from by decide]
  | change (∑ x ∈ S0.filter (fun x => x 3 = true), Complex.normSq (c x)) = _
    rw [show S0.filter (fun x => x 3 = true) =
        {one 3, SS.complement (pair 0 1), SS.complement (pair 0 2),
         SS.complement (pair 0 4), SS.complement (pair 0 5),
         SS.complement (pair 1 2), SS.complement (pair 1 4),
         SS.complement (pair 1 5), SS.complement (pair 2 4),
         SS.complement (pair 2 5), SS.complement (pair 4 5)} from by decide]
  | change (∑ x ∈ S0.filter (fun x => x 4 = true), Complex.normSq (c x)) = _
    rw [show S0.filter (fun x => x 4 = true) =
        {one 4, SS.complement (pair 0 1), SS.complement (pair 0 2),
         SS.complement (pair 0 3), SS.complement (pair 0 5),
         SS.complement (pair 1 2), SS.complement (pair 1 3),
         SS.complement (pair 1 5), SS.complement (pair 2 3),
         SS.complement (pair 2 5), SS.complement (pair 3 5)} from by decide]
  | change (∑ x ∈ S0.filter (fun x => x 5 = true), Complex.normSq (c x)) = _
    rw [show S0.filter (fun x => x 5 = true) =
        {one 5, SS.complement (pair 0 1), SS.complement (pair 0 2),
         SS.complement (pair 0 3), SS.complement (pair 0 4),
         SS.complement (pair 1 2), SS.complement (pair 1 3),
         SS.complement (pair 1 4), SS.complement (pair 2 3),
         SS.complement (pair 2 4), SS.complement (pair 3 4)} from by decide]
  all_goals
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp [p, Rdeg, r, one, pair, Fin.sum_univ_succ]
    ring

set_option maxHeartbeats 4000000 in
lemma occOn_S1_formula (d : SS.State 6 ℂ) (i : Fin 6) :
    SixQubit.occOn S1 d i = Sdeg d i + Qmass d - q d i := by
  unfold SixQubit.occOn
  fin_cases i
  all_goals first
  | change (∑ x ∈ S1.filter (fun x => x 0 = true), Complex.normSq (d x)) = _
    rw [show S1.filter (fun x => x 0 = true) =
        {pair 0 1, pair 0 2, pair 0 3, pair 0 4, pair 0 5,
         SS.complement (one 1), SS.complement (one 2),
         SS.complement (one 3), SS.complement (one 4),
         SS.complement (one 5)} from by decide]
  | change (∑ x ∈ S1.filter (fun x => x 1 = true), Complex.normSq (d x)) = _
    rw [show S1.filter (fun x => x 1 = true) =
        {pair 0 1, pair 1 2, pair 1 3, pair 1 4, pair 1 5,
         SS.complement (one 0), SS.complement (one 2),
         SS.complement (one 3), SS.complement (one 4),
         SS.complement (one 5)} from by decide]
  | change (∑ x ∈ S1.filter (fun x => x 2 = true), Complex.normSq (d x)) = _
    rw [show S1.filter (fun x => x 2 = true) =
        {pair 0 2, pair 1 2, pair 2 3, pair 2 4, pair 2 5,
         SS.complement (one 0), SS.complement (one 1),
         SS.complement (one 3), SS.complement (one 4),
         SS.complement (one 5)} from by decide]
  | change (∑ x ∈ S1.filter (fun x => x 3 = true), Complex.normSq (d x)) = _
    rw [show S1.filter (fun x => x 3 = true) =
        {pair 0 3, pair 1 3, pair 2 3, pair 3 4, pair 3 5,
         SS.complement (one 0), SS.complement (one 1),
         SS.complement (one 2), SS.complement (one 4),
         SS.complement (one 5)} from by decide]
  | change (∑ x ∈ S1.filter (fun x => x 4 = true), Complex.normSq (d x)) = _
    rw [show S1.filter (fun x => x 4 = true) =
        {pair 0 4, pair 1 4, pair 2 4, pair 3 4, pair 4 5,
         SS.complement (one 0), SS.complement (one 1),
         SS.complement (one 2), SS.complement (one 3),
         SS.complement (one 5)} from by decide]
  | change (∑ x ∈ S1.filter (fun x => x 5 = true), Complex.normSq (d x)) = _
    rw [show S1.filter (fun x => x 5 = true) =
        {pair 0 5, pair 1 5, pair 2 5, pair 3 5, pair 4 5,
         SS.complement (one 0), SS.complement (one 1),
         SS.complement (one 2), SS.complement (one 3),
         SS.complement (one 4)} from by decide]
  all_goals
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [Sdeg, Qmass, q, s, one, pair, Fin.sum_univ_succ]
    ring

def occ2Star (S : Finset (SS.BitString 6)) (c : SS.State 6 ℂ)
    (i : Fin 6) : ℝ :=
  ∑ j ∈ (Finset.univ.erase i), SixQubit.occ2On S c i j

def awayCount (x : SS.BitString 6) (i : Fin 6) : ℕ :=
  if x i = true then
    ((Finset.univ.erase i).filter (fun j => x j = true)).card
  else 0

lemma sum_occ2Star (S : Finset (SS.BitString 6)) (c : SS.State 6 ℂ)
    (i : Fin 6) :
    occ2Star S c i =
      ∑ x ∈ S, (awayCount x i : ℝ) * Complex.normSq (c x) := by
  classical
  unfold occ2Star SixQubit.occ2On
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  by_cases hi : x i = true
  · simp [awayCount, hi]
  · simp [awayCount, hi]

@[simp] lemma awayCount_one (i k : Fin 6) :
    awayCount (one k) i = 0 := by
  revert i k
  decide

@[simp] lemma awayCount_pair (i k l : Fin 6) (hkl : k ≠ l) :
    awayCount (pair k l) i = if i = k ∨ i = l then 1 else 0 := by
  revert i k l
  decide

@[simp] lemma awayCount_complement_one (i k : Fin 6) :
    awayCount (SS.complement (one k)) i = if i = k then 0 else 4 := by
  revert i k
  decide

@[simp] lemma awayCount_complement_pair (i k l : Fin 6) (hkl : k ≠ l) :
    awayCount (SS.complement (pair k l)) i =
      if i = k ∨ i = l then 0 else 3 := by
  revert i k l
  decide

set_option maxHeartbeats 3000000 in
lemma occ2Star_S0_formula (c : SS.State 6 ℂ) (i : Fin 6) :
    occ2Star S0 c i = 3 * (Rmass c - Rdeg c i) := by
  rw [sum_occ2Star, sum_S0, Rmass_edges]
  fin_cases i <;> simp [awayCount_complement_pair]
  all_goals
    simp [Rdeg, r, one, pair, Fin.sum_univ_succ]
    ring

set_option maxHeartbeats 3000000 in
lemma occ2Star_S1_formula (d : SS.State 6 ℂ) (i : Fin 6) :
    occ2Star S1 d i = Sdeg d i + 4 * (Qmass d - q d i) := by
  rw [sum_occ2Star, sum_S1]
  fin_cases i <;> simp [awayCount_pair]
  all_goals
    simp [Sdeg, Qmass, q, s, one, pair, Fin.sum_univ_succ]
    ring

/-- Coordinatewise normal form for the two weighted support graphs.  This is
still purely the diagonal part of Knill--Laflamme: no phase equations or
nonzero-support ansatz enter. -/
theorem degree_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    Rdeg c i = (1/3 - p c i + 3 * q d i) / 2 ∧
      Sdeg d i = (1/3 - q d i + 3 * p c i) / 2 := by
  rcases global_masses c d hc hd hnc hnd hdist with
    ⟨hP, hR, hS, hQ⟩
  have ho := SixQubit.occOn_eq_of_hasDistance S0 S1 c d
    hc hd hnc hnd hdist i
  rw [occOn_S0_formula, occOn_S1_formula] at ho
  have ho2 : occ2Star S0 c i = occ2Star S1 d i := by
    unfold occ2Star
    apply Finset.sum_congr rfl
    intro j _
    exact SixQubit.occ2On_eq_of_hasDistance S0 S1 c d
      hc hd hnc hnd hdist i j
  rw [occ2Star_S0_formula, occ2Star_S1_formula] at ho2
  constructor <;> linarith

/-! ## The final enumerator squeeze once the inactive pair is known -/

/-- Every basis word carrying a nonzero coefficient has equal bits in the two
displayed coordinates.  This is the exact support statement produced by the
orbit-9 active-graph reduction. -/
def EqualBitsSupport (c : SS.State 6 ℂ) (i j : Fin 6) : Prop :=
  ∀ x, x i ≠ x j → c x = 0

/-- Equal support bits make `Z_i Z_j` fix the state. -/
lemma zpair_fixes_of_equalBits (c : SS.State 6 ℂ) (i j : Fin 6)
    (h : EqualBitsSupport c i j) :
    SS.pauliAct
      (⟨fun _ => false, SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩ :
        SS.PauliString 6) c = c := by
  funext x
  have hY :
      (⟨fun _ => false, SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩ :
        SS.PauliString 6).numY = 0 := SixQubit.numY_of_x_zero _
  simp only [SS.pauliAct, hY, pow_zero, one_mul, SS.bxor_zero]
  rw [SixQubit.bdot_stdBasis_pair]
  by_cases hij : x i = x j
  · cases hi : x i <;> cases hj : x j <;> simp_all [SS.signC]
  · rw [h x hij]
    cases hi : x i <;> cases hj : x j <;> simp_all [SS.signC]

lemma zpair_wt (i j : Fin 6) (hij : i ≠ j) :
    (⟨fun _ => false, SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩ :
      SS.PauliString 6).wt = 2 := by
  rw [wt_eq_card_supp]
  have hs : supp
      (⟨fun _ => false, SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩ :
        SS.PauliString 6) = {i,j} := by
    ext k
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and,
      Bool.false_or, Finset.mem_insert, Finset.mem_singleton]
    simp [SS.stdBasis, SS.bxor]
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
  rw [hs]
  simp [hij]

/-- Once the support reduction has found two inactive coordinates, the shadow
bound and MacWilliams identities force the complete `E2` enumerator pair. -/
theorem enumerator_of_equal_pair (c d : SS.State 6 ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3)
    (i j : Fin 6) (hij : i ≠ j)
    (hc : EqualBitsSupport c i j) (hd : EqualBitsSupport d i j) :
    IsE2A ![c,d] ∧ IsE2B ![c,d] := by
  let psi : Fin 2 → SS.State 6 ℂ := ![c,d]
  let G : SS.PauliString 6 :=
    ⟨fun _ => false, SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩
  have hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1 := by
    intro k
    fin_cases k
    · exact hnc
    · exact hnd
  have hG : ∀ k, SS.pauliAct G (psi k) = psi k := by
    intro k
    fin_cases k
    · exact zpair_fixes_of_equalBits c i j hc
    · exact zpair_fixes_of_equalBits d i j hd
  have hw : G.wt = 2 := zpair_wt i j hij
  have hA0 : Aco psi 0 = 4 := SixQubit.Pin.Aco_zero psi hnorm
  rcases (SixQubit.Pin.enumerator_of_forced psi hdist hA0 hnorm G hG).2 hw with
    ⟨hA1,hA2,hA3,hA4,hA5,hA6⟩
  have hA : IsE2A psi := ⟨hA0,hA1,hA2,hA3,hA4,hA5,hA6⟩
  exact ⟨hA, e2B_of_e2A psi hA⟩

/-! ## The original orbit-9 gauge -/

/-- Flipping the sixth qubit changes `(1,1,1,1,1,2)` into the uniform
order-three lift. -/
def flip6 : SS.BitString 6 := SS.stdBasis 5

def toUniform (c : SS.State 6 ℂ) : SS.State 6 ℂ :=
  SixQubit.CodeEquiv.flipAct flip6 c

theorem original0_iff_uniform1 (x : SS.BitString 6) :
    SS.weight SixQubit.Orbit9Real.av (SS.bxor x flip6) = 0 ↔
      SS.weight uniformAv x = 1 := by
  revert x
  decide

theorem original1_iff_uniform2 (x : SS.BitString 6) :
    SS.weight SixQubit.Orbit9Real.av (SS.bxor x flip6) = 1 ↔
      SS.weight uniformAv x = 2 := by
  revert x
  decide

lemma toUniform_support0 (c : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 0 → c x = 0) :
    ∀ x, x ∉ S0 → toUniform c x = 0 := by
  intro x hx
  apply hc
  intro hw
  apply hx
  rw [← S0_eq_fiber]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ x, (original0_iff_uniform1 x).mp hw⟩

lemma toUniform_support1 (d : SS.State 6 ℂ)
    (hd : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 1 → d x = 0) :
    ∀ x, x ∉ S1 → toUniform d x = 0 := by
  intro x hx
  apply hd
  intro hw
  apply hx
  rw [← S1_eq_fiber]
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ x, (original1_iff_uniform2 x).mp hw⟩

lemma innerC_toUniform (c d : SS.State 6 ℂ) :
    SS.innerC (toUniform c) (toUniform d) = SS.innerC c d := by
  unfold SS.innerC toUniform SixQubit.CodeEquiv.flipAct
  simpa using
    (Equiv.sum_comp (SS.bxorEquiv flip6)
      (fun x : SS.BitString 6 => star (c x) * d x))

lemma hasDistance_toUniform (c d : SS.State 6 ℂ)
    (h : SS.HasDistance ![c,d] 3) :
    SS.HasDistance ![toUniform c, toUniform d] 3 := by
  have hr := (SixQubit.CodeEquiv.hasDistance_iff ![c,d]).mp h
  have hf := SixQubit.CodeEquiv.detectsRaw_flipAct flip6 hr
  exact (SixQubit.CodeEquiv.hasDistance_iff ![toUniform c,toUniform d]).mpr (by
    simpa [toUniform] using hf)

/-- Code-level original-gauge wrapper for the last support-reduction output.
The remaining universal orbit-9 argument has exactly one job: produce the
common equal-bit pair for the two translated words. -/
theorem original_of_uniform_equal_pair (c d : SS.State 6 ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3)
    (i j : Fin 6) (hij : i ≠ j)
    (hc : EqualBitsSupport (toUniform c) i j)
    (hd : EqualBitsSupport (toUniform d) i j) :
    IsE2A ![c,d] ∧ IsE2B ![c,d] := by
  have hncu : SS.innerC (toUniform c) (toUniform c) = 1 := by
    rw [innerC_toUniform, hnc]
  have hndu : SS.innerC (toUniform d) (toUniform d) = 1 := by
    rw [innerC_toUniform, hnd]
  have hu := enumerator_of_equal_pair (toUniform c) (toUniform d)
    hncu hndu (hasDistance_toUniform c d hdist) i j hij hc hd
  have hAinv : ∀ w, Aco ![toUniform c,toUniform d] w = Aco ![c,d] w := by
    intro w
    have h := SixQubit.CodeEquiv.Aco_flipAct flip6 ![c,d] w
    simpa [toUniform] using h
  rcases hu.1 with ⟨hA0,hA1,hA2,hA3,hA4,hA5,hA6⟩
  have hA : IsE2A ![c,d] := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · rw [← hAinv 0]; exact hA0
    · rw [← hAinv 1]; exact hA1
    · rw [← hAinv 2]; exact hA2
    · rw [← hAinv 3]; exact hA3
    · rw [← hAinv 4]; exact hA4
    · rw [← hAinv 5]; exact hA5
    · rw [← hAinv 6]; exact hA6
  exact ⟨hA, e2B_of_e2A _ hA⟩

end

end SixQubit.Orbit9Universal
