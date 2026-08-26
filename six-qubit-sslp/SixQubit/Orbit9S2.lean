import SixQubit.Orbit9Pair
import SixQubit.Orbit8UniversalQ

/-!
# Orbit 9: exclusion of a two-point singleton support

This file isolates the diagonal Knill--Laflamme contradiction used to rule
out the `|Sigma| = 2` branch.  It works in the uniform orbit-9 gauge and on
the complete fibres `S0` and `S1`.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate

noncomputable section

private lemma inner_eq_sum_of_support (S : Finset (SS.BitString 6))
    (f g : SS.State 6 ℂ) (hf : ∀ x, x ∉ S → f x = 0) :
    SS.innerC f g = ∑ x ∈ S, star (f x) * g x := by
  classical
  unfold SS.innerC
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  intro x _ hx
  rw [hf x hx]
  simp

private lemma sum_S0_complex (f : SS.BitString 6 → ℂ) :
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

private lemma sum_S1_complex (f : SS.BitString 6 → ℂ) :
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

/-- Exact `S0` expansion of the detectable hop from coordinate `1` to
coordinate `0`.  No displayed witness support is used. -/
lemma inner_hop01_S0 (c : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) :
    SS.innerC c (SixQubit.Orbit8Universal.hop 0 1 c) =
      star (xamp c 0) * xamp c 1 +
      star (damp c 1 2) * damp c 0 2 +
      star (damp c 1 3) * damp c 0 3 +
      star (damp c 1 4) * damp c 0 4 +
      star (damp c 1 5) * damp c 0 5 := by
  have h01 : SS.bxor (one 0) (SixQubit.Orbit8Universal.pairMask 0 1) = one 1 := by
    decide
  have h12 : SS.bxor (SS.complement (pair 1 2))
      (SixQubit.Orbit8Universal.pairMask 0 1) = SS.complement (pair 0 2) := by decide
  have h13 : SS.bxor (SS.complement (pair 1 3))
      (SixQubit.Orbit8Universal.pairMask 0 1) = SS.complement (pair 0 3) := by decide
  have h14 : SS.bxor (SS.complement (pair 1 4))
      (SixQubit.Orbit8Universal.pairMask 0 1) = SS.complement (pair 0 4) := by decide
  have h15 : SS.bxor (SS.complement (pair 1 5))
      (SixQubit.Orbit8Universal.pairMask 0 1) = SS.complement (pair 0 5) := by decide
  rw [inner_eq_sum_of_support S0 c _ hc, sum_S0_complex]
  simp only [SixQubit.Orbit8Universal.hop]
  rw [h01, h12, h13, h14, h15]
  simp [xamp, damp, one, pair]

/-- Exact `S1` expansion of the same detectable hop. -/
lemma inner_hop01_S1 (d : SS.State 6 ℂ)
    (hd : ∀ x, x ∉ S1 → d x = 0) :
    SS.innerC d (SixQubit.Orbit8Universal.hop 0 1 d) =
      star (yamp d 1) * yamp d 0 +
      star (camp d 0 2) * camp d 1 2 +
      star (camp d 0 3) * camp d 1 3 +
      star (camp d 0 4) * camp d 1 4 +
      star (camp d 0 5) * camp d 1 5 := by
  have h10 : SS.bxor (SS.complement (one 1))
      (SixQubit.Orbit8Universal.pairMask 0 1) = SS.complement (one 0) := by decide
  have h02 : SS.bxor (pair 0 2) (SixQubit.Orbit8Universal.pairMask 0 1) =
      pair 1 2 := by decide
  have h03 : SS.bxor (pair 0 3) (SixQubit.Orbit8Universal.pairMask 0 1) =
      pair 1 3 := by decide
  have h04 : SS.bxor (pair 0 4) (SixQubit.Orbit8Universal.pairMask 0 1) =
      pair 1 4 := by decide
  have h05 : SS.bxor (pair 0 5) (SixQubit.Orbit8Universal.pairMask 0 1) =
      pair 1 5 := by decide
  rw [inner_eq_sum_of_support S1 d _ hd, sum_S1_complex]
  simp only [SixQubit.Orbit8Universal.hop]
  rw [h10, h02, h03, h04, h05]
  simp [yamp, camp, one, pair]
  ring

structure TwoSupport01 (c : SS.State 6 ℂ) : Prop where
  p0_pos : 0 < p c 0
  p1_pos : 0 < p c 1
  p2_zero : p c 2 = 0
  p3_zero : p c 3 = 0
  p4_zero : p c 4 = 0
  p5_zero : p c 5 = 0

private lemma Rdeg0 (c : SS.State 6 ℂ) :
    Rdeg c 0 = r c 0 1 + r c 0 2 + r c 0 3 + r c 0 4 + r c 0 5 := by
  simp [Rdeg, Fin.sum_univ_succ, r]
  ring

private lemma Rdeg1 (c : SS.State 6 ℂ) :
    Rdeg c 1 = r c 1 0 + r c 1 2 + r c 1 3 + r c 1 4 + r c 1 5 := by
  simp [Rdeg, Fin.sum_univ_succ, r]
  ring

private lemma Rdeg2 (c : SS.State 6 ℂ) :
    Rdeg c 2 = r c 2 0 + r c 2 1 + r c 2 3 + r c 2 4 + r c 2 5 := by
  simp [Rdeg, Fin.sum_univ_succ, r]
  ring

private lemma Rdeg3 (c : SS.State 6 ℂ) :
    Rdeg c 3 = r c 3 0 + r c 3 1 + r c 3 2 + r c 3 4 + r c 3 5 := by
  simp [Rdeg, Fin.sum_univ_succ, r]
  ring

private lemma Rdeg4 (c : SS.State 6 ℂ) :
    Rdeg c 4 = r c 4 0 + r c 4 1 + r c 4 2 + r c 4 3 + r c 4 5 := by
  simp [Rdeg, Fin.sum_univ_succ, r]
  ring

private lemma Rdeg5 (c : SS.State 6 ℂ) :
    Rdeg c 5 = r c 5 0 + r c 5 1 + r c 5 2 + r c 5 3 + r c 5 4 := by
  simp [Rdeg, Fin.sum_univ_succ, r]
  ring

private lemma norm_balance_of_row (a b ya yb : ℂ)
    (h : a * star ya + b * star yb = 0) :
    Complex.normSq a * Complex.normSq ya =
      Complex.normSq b * Complex.normSq yb := by
  have he : a * star ya = -(b * star yb) := by linear_combination h
  have hn := congrArg Complex.normSq he
  simpa [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj] using hn

private lemma normSq_damp_eq_r (c : SS.State 6 ℂ) (i j : Fin 6)
    (hij : i ≠ j) : Complex.normSq (damp c i j) = r c i j := by
  simp [damp, r, hij]

private lemma normSq_yamp_eq_q (d : SS.State 6 ℂ) (i : Fin 6) :
    Complex.normSq (yamp d i) = q d i := rfl

private lemma r_equal_of_two_term_row (c d : SS.State 6 ℂ) (t : Fin 6)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (hp0 : p c 0 = 1/6) (hp1 : p c 1 = 1/6)
    (hpq0 : p c 0 = q d 0) (hpq1 : p c 1 = q d 1)
    (hrow : damp c t 0 * star (yamp d 0) +
      damp c t 1 * star (yamp d 1) = 0) :
    r c t 0 = r c t 1 := by
  have hn := norm_balance_of_row _ _ _ _ hrow
  have h : r c t 0 * q d 0 = r c t 1 * q d 1 := by
    simpa only [normSq_damp_eq_r c t 0 ht0,
      normSq_damp_eq_r c t 1 ht1, normSq_yamp_eq_q] using hn
  rw [← hpq0, ← hpq1, hp0, hp1] at h
  nlinarith

private lemma companion0_explicit (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    damp c 0 1 * star (yamp d 1) + damp c 0 2 * star (yamp d 2) +
      damp c 0 3 * star (yamp d 3) + damp c 0 4 * star (yamp d 4) +
      damp c 0 5 * star (yamp d 5) = 0 := by
  have h := companion_row c d hc hd hdist 0
  rw [show (Finset.univ.erase 0 : Finset (Fin 6)) = {1,2,3,4,5} by decide] at h
  simpa [add_assoc] using h

private lemma companion1_explicit (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    damp c 1 0 * star (yamp d 0) + damp c 1 2 * star (yamp d 2) +
      damp c 1 3 * star (yamp d 3) + damp c 1 4 * star (yamp d 4) +
      damp c 1 5 * star (yamp d 5) = 0 := by
  have h := companion_row c d hc hd hdist 1
  rw [show (Finset.univ.erase 1 : Finset (Fin 6)) = {0,2,3,4,5} by decide] at h
  simpa [add_assoc] using h

private lemma companion2_explicit (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    damp c 2 0 * star (yamp d 0) + damp c 2 1 * star (yamp d 1) +
      damp c 2 3 * star (yamp d 3) + damp c 2 4 * star (yamp d 4) +
      damp c 2 5 * star (yamp d 5) = 0 := by
  have h := companion_row c d hc hd hdist 2
  rw [show (Finset.univ.erase 2 : Finset (Fin 6)) = {0,1,3,4,5} by decide] at h
  simpa [add_assoc] using h

private lemma companion3_explicit (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    damp c 3 0 * star (yamp d 0) + damp c 3 1 * star (yamp d 1) +
      damp c 3 2 * star (yamp d 2) + damp c 3 4 * star (yamp d 4) +
      damp c 3 5 * star (yamp d 5) = 0 := by
  have h := companion_row c d hc hd hdist 3
  rw [show (Finset.univ.erase 3 : Finset (Fin 6)) = {0,1,2,4,5} by decide] at h
  simpa [add_assoc] using h

private lemma companion4_explicit (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    damp c 4 0 * star (yamp d 0) + damp c 4 1 * star (yamp d 1) +
      damp c 4 2 * star (yamp d 2) + damp c 4 3 * star (yamp d 3) +
      damp c 4 5 * star (yamp d 5) = 0 := by
  have h := companion_row c d hc hd hdist 4
  rw [show (Finset.univ.erase 4 : Finset (Fin 6)) = {0,1,2,3,5} by decide] at h
  simpa [add_assoc] using h

private lemma companion5_explicit (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) :
    damp c 5 0 * star (yamp d 0) + damp c 5 1 * star (yamp d 1) +
      damp c 5 2 * star (yamp d 2) + damp c 5 3 * star (yamp d 3) +
      damp c 5 4 * star (yamp d 4) = 0 := by
  have h := companion_row c d hc hd hdist 5
  rw [show (Finset.univ.erase 5 : Finset (Fin 6)) = {0,1,2,3,4} by decide] at h
  simpa [add_assoc] using h

/-- Raw probability identities in the two-active-vertex branch. -/
private lemma twoSupport01_probability_data (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (hs : TwoSupport01 c) :
    p c 0 + p c 1 = 1/3 ∧
      p c 0 * (1/6 + p c 0) = p c 1 * (1/6 + p c 1) ∧
      damp c 0 1 = 0 := by
  have hpq0 := (pq_degree c d hc hd hnc hnd hdist 0).1
  have hpq1 := (pq_degree c d hc hd hnc hnd hdist 1).1
  have hpq2 := (pq_degree c d hc hd hnc hnd hdist 2).1
  have hpq3 := (pq_degree c d hc hd hnc hnd hdist 3).1
  have hpq4 := (pq_degree c d hc hd hnc hnd hdist 4).1
  have hpq5 := (pq_degree c d hc hd hnc hnd hdist 5).1
  have hy1 : yamp d 1 ≠ 0 := by
    have hq1pos : 0 < q d 1 := by nlinarith [hs.p1_pos, hpq1]
    exact Complex.normSq_pos.mp (by simpa only [q, yamp] using hq1pos)
  have hy2 : yamp d 2 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq2.symm.trans hs.p2_zero
  have hy3 : yamp d 3 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq3.symm.trans hs.p3_zero
  have hy4 : yamp d 4 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq4.symm.trans hs.p4_zero
  have hy5 : yamp d 5 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq5.symm.trans hs.p5_zero
  have habrow := companion0_explicit c d hc hd hdist
  rw [hy2, hy3, hy4, hy5] at habrow
  have habrow' : damp c 0 1 * star (yamp d 1) = 0 := by simpa using habrow
  have hab : damp c 0 1 = 0 :=
    (mul_eq_zero.mp habrow').resolve_right (star_ne_zero.mpr hy1)
  have hr01amp : r c 0 1 = Complex.normSq (damp c 0 1) := by
    simp [r, damp]
  have hr01 : r c 0 1 = 0 := by rw [hr01amp, hab, Complex.normSq_zero]
  have hr10 : r c 1 0 = 0 := by rw [r_symm]; exact hr01
  have hP := (global_masses c d hc hd hnc hnd hdist).1
  have hpsum : p c 0 + p c 1 = 1/3 := by
    simp [Pmass, Fin.sum_univ_succ, hs.p2_zero, hs.p3_zero, hs.p4_zero,
      hs.p5_zero] at hP
    linarith
  have hR0 := (pq_degree c d hc hd hnc hnd hdist 0).2.1
  have hR1 := (pq_degree c d hc hd hnc hnd hdist 1).2.1
  rw [Rdeg0, hr01] at hR0
  rw [Rdeg1, hr10] at hR1
  have hb2 := companion2_explicit c d hc hd hdist
  have hb3 := companion3_explicit c d hc hd hdist
  have hb4 := companion4_explicit c d hc hd hdist
  have hb5 := companion5_explicit c d hc hd hdist
  simp only [hy2, hy3, hy4, hy5] at hb2 hb3 hb4 hb5
  have hb2' : damp c 2 0 * star (yamp d 0) +
      damp c 2 1 * star (yamp d 1) = 0 := by simpa using hb2
  have hb3' : damp c 3 0 * star (yamp d 0) +
      damp c 3 1 * star (yamp d 1) = 0 := by simpa using hb3
  have hb4' : damp c 4 0 * star (yamp d 0) +
      damp c 4 1 * star (yamp d 1) = 0 := by simpa using hb4
  have hb5' : damp c 5 0 * star (yamp d 0) +
      damp c 5 1 * star (yamp d 1) = 0 := by simpa using hb5
  have hn2 := congrArg Complex.normSq (show
      damp c 2 0 * star (yamp d 0) = -(damp c 2 1 * star (yamp d 1)) by
        linear_combination hb2')
  have hn3 := congrArg Complex.normSq (show
      damp c 3 0 * star (yamp d 0) = -(damp c 3 1 * star (yamp d 1)) by
        linear_combination hb3')
  have hn4 := congrArg Complex.normSq (show
      damp c 4 0 * star (yamp d 0) = -(damp c 4 1 * star (yamp d 1)) by
        linear_combination hb4')
  have hn5 := congrArg Complex.normSq (show
      damp c 5 0 * star (yamp d 0) = -(damp c 5 1 * star (yamp d 1)) by
        linear_combination hb5')
  have hn2R : r c 2 0 * q d 0 = r c 2 1 * q d 1 := by
    simpa [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      r, q, damp, yamp] using hn2
  have hn3R : r c 3 0 * q d 0 = r c 3 1 * q d 1 := by
    simpa [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      r, q, damp, yamp] using hn3
  have hn4R : r c 4 0 * q d 0 = r c 4 1 * q d 1 := by
    simpa [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      r, q, damp, yamp] using hn4
  have hn5R : r c 5 0 * q d 0 = r c 5 1 * q d 1 := by
    simpa [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      r, q, damp, yamp] using hn5
  have hn2P : r c 2 0 * p c 0 = r c 2 1 * p c 1 := by
    rw [hpq0, hpq1]; exact hn2R
  have hn3P : r c 3 0 * p c 0 = r c 3 1 * p c 1 := by
    rw [hpq0, hpq1]; exact hn3R
  have hn4P : r c 4 0 * p c 0 = r c 4 1 * p c 1 := by
    rw [hpq0, hpq1]; exact hn4R
  have hn5P : r c 5 0 * p c 0 = r c 5 1 * p c 1 := by
    rw [hpq0, hpq1]; exact hn5R
  have hmono : p c 0 * (1/6 + p c 0) = p c 1 * (1/6 + p c 1) := by
    rw [← hR0, ← hR1]
    rw [← r_symm c 2 0, ← r_symm c 3 0, ← r_symm c 4 0,
      ← r_symm c 5 0, ← r_symm c 2 1, ← r_symm c 3 1,
      ← r_symm c 4 1, ← r_symm c 5 1]
    linear_combination hn2P + hn3P + hn4P + hn5P
  exact ⟨hpsum, hmono, hab⟩

/-- The probability part of the two-active-vertex branch. -/
lemma twoSupport01_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (hs : TwoSupport01 c) :
    p c 0 = 1/6 ∧ p c 1 = 1/6 ∧ damp c 0 1 = 0 := by
  rcases twoSupport01_probability_data c d hc hd hnc hnd hdist hs with
    ⟨hsum, hmono, hab⟩
  have hp0 : p c 0 = 1/6 := by nlinarith
  have hp1 : p c 1 = 1/6 := by nlinarith
  exact ⟨hp0, hp1, hab⟩

structure TwoSupport01Rows (c : SS.State 6 ℂ) : Prop where
  r20_eq_r21 : r c 2 0 = r c 2 1
  r30_eq_r31 : r c 3 0 = r c 3 1
  r40_eq_r41 : r c 4 0 = r c 4 1
  r50_eq_r51 : r c 5 0 = r c 5 1

private lemma twoSupport01_row_equalities (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (hs : TwoSupport01 c) :
    TwoSupport01Rows c := by
  rcases twoSupport01_probabilities c d hc hd hnc hnd hdist hs with
    ⟨hp0, hp1, _⟩
  have hpq0 := (pq_degree c d hc hd hnc hnd hdist 0).1
  have hpq1 := (pq_degree c d hc hd hnc hnd hdist 1).1
  have hpq2 := (pq_degree c d hc hd hnc hnd hdist 2).1
  have hpq3 := (pq_degree c d hc hd hnc hnd hdist 3).1
  have hpq4 := (pq_degree c d hc hd hnc hnd hdist 4).1
  have hpq5 := (pq_degree c d hc hd hnc hnd hdist 5).1
  have hy2 : yamp d 2 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq2.symm.trans hs.p2_zero
  have hy3 : yamp d 3 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq3.symm.trans hs.p3_zero
  have hy4 : yamp d 4 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq4.symm.trans hs.p4_zero
  have hy5 : yamp d 5 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq5.symm.trans hs.p5_zero
  have hb2 := companion2_explicit c d hc hd hdist
  have hb3 := companion3_explicit c d hc hd hdist
  have hb4 := companion4_explicit c d hc hd hdist
  have hb5 := companion5_explicit c d hc hd hdist
  simp only [hy2, hy3, hy4, hy5] at hb2 hb3 hb4 hb5
  have hb2' : damp c 2 0 * star (yamp d 0) +
      damp c 2 1 * star (yamp d 1) = 0 := by simpa using hb2
  have hb3' : damp c 3 0 * star (yamp d 0) +
      damp c 3 1 * star (yamp d 1) = 0 := by simpa using hb3
  have hb4' : damp c 4 0 * star (yamp d 0) +
      damp c 4 1 * star (yamp d 1) = 0 := by simpa using hb4
  have hb5' : damp c 5 0 * star (yamp d 0) +
      damp c 5 1 * star (yamp d 1) = 0 := by simpa using hb5
  exact ⟨r_equal_of_two_term_row c d 2 (by decide) (by decide)
      hp0 hp1 hpq0 hpq1 hb2',
    r_equal_of_two_term_row c d 3 (by decide) (by decide)
      hp0 hp1 hpq0 hpq1 hb3',
    r_equal_of_two_term_row c d 4 (by decide) (by decide)
      hp0 hp1 hpq0 hpq1 hb4',
    r_equal_of_two_term_row c d 5 (by decide) (by decide)
      hp0 hp1 hpq0 hpq1 hb5'⟩

structure TwoSupport01Magnitudes (c : SS.State 6 ℂ) : Prop where
  r20 : r c 2 0 = 1/12
  r30 : r c 3 0 = 1/12
  r40 : r c 4 0 = 1/12
  r50 : r c 5 0 = 1/12
  r21 : r c 2 1 = 1/12
  r31 : r c 3 1 = 1/12
  r41 : r c 4 1 = 1/12
  r51 : r c 5 1 = 1/12

structure TwoSupport01Edges (c : SS.State 6 ℂ) : Prop where
  r02 : r c 0 2 = 1/12
  r03 : r c 0 3 = 1/12
  r04 : r c 0 4 = 1/12
  r05 : r c 0 5 = 1/12
  r12 : r c 1 2 = 1/12
  r13 : r c 1 3 = 1/12
  r14 : r c 1 4 = 1/12
  r15 : r c 1 5 = 1/12
  damp23_zero : damp c 2 3 = 0

private structure TwoSupport01DegreeData (c : SS.State 6 ℂ) : Prop where
  r20_eq_r21 : r c 2 0 = r c 2 1
  r30_eq_r31 : r c 3 0 = r c 3 1
  r40_eq_r41 : r c 4 0 = r c 4 1
  r50_eq_r51 : r c 5 0 = r c 5 1
  r20_upper : r c 2 0 ≤ 1/12
  r30_upper : r c 3 0 ≤ 1/12
  r40_upper : r c 4 0 ≤ 1/12
  r50_upper : r c 5 0 ≤ 1/12
  active_sum : r c 2 0 + r c 3 0 + r c 4 0 + r c 5 0 = 1/3

private lemma twoSupport01_degree_data (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (hs : TwoSupport01 c) :
    TwoSupport01DegreeData c := by
  rcases twoSupport01_probabilities c d hc hd hnc hnd hdist hs with
    ⟨hp0, hp1, hab⟩
  rcases twoSupport01_row_equalities c d hc hd hnc hnd hdist hs with
    ⟨hr20, hr30, hr40, hr50⟩
  have hR0 := (pq_degree c d hc hd hnc hnd hdist 0).2.1
  have hR2 := (pq_degree c d hc hd hnc hnd hdist 2).2.1
  have hR3 := (pq_degree c d hc hd hnc hnd hdist 3).2.1
  have hR4 := (pq_degree c d hc hd hnc hnd hdist 4).2.1
  have hR5 := (pq_degree c d hc hd hnc hnd hdist 5).2.1
  rw [Rdeg0, hp0] at hR0
  rw [Rdeg2, hs.p2_zero] at hR2
  rw [Rdeg3, hs.p3_zero] at hR3
  rw [Rdeg4, hs.p4_zero] at hR4
  rw [Rdeg5, hs.p5_zero] at hR5
  have hu2 : r c 2 0 ≤ 1/12 := by
    nlinarith [r_nonneg c 2 3, r_nonneg c 2 4, r_nonneg c 2 5]
  have hu3 : r c 3 0 ≤ 1/12 := by
    nlinarith [r_nonneg c 3 2, r_nonneg c 3 4, r_nonneg c 3 5]
  have hu4 : r c 4 0 ≤ 1/12 := by
    nlinarith [r_nonneg c 4 2, r_nonneg c 4 3, r_nonneg c 4 5]
  have hu5 : r c 5 0 ≤ 1/12 := by
    nlinarith [r_nonneg c 5 2, r_nonneg c 5 3, r_nonneg c 5 4]
  have hsum : r c 2 0 + r c 3 0 + r c 4 0 + r c 5 0 = 1/3 := by
    rw [r_symm c 2 0, r_symm c 3 0, r_symm c 4 0, r_symm c 5 0]
    have hr01amp : r c 0 1 = Complex.normSq (damp c 0 1) := by
      simp [r, damp]
    have hr01 : r c 0 1 = 0 := by rw [hr01amp, hab, Complex.normSq_zero]
    nlinarith
  exact ⟨hr20, hr30, hr40, hr50, hu2, hu3, hu4, hu5, hsum⟩

private lemma twoSupport01_magnitudes (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (hs : TwoSupport01 c) :
    TwoSupport01Magnitudes c := by
  rcases twoSupport01_degree_data c d hc hd hnc hnd hdist hs with
    ⟨hr20, hr30, hr40, hr50, hu2, hu3, hu4, hu5, hsum⟩
  have er20 : r c 2 0 = 1/12 := by nlinarith
  have er30 : r c 3 0 = 1/12 := by nlinarith
  have er40 : r c 4 0 = 1/12 := by nlinarith
  have er50 : r c 5 0 = 1/12 := by nlinarith
  have er21 : r c 2 1 = 1/12 := by nlinarith
  have er31 : r c 3 1 = 1/12 := by nlinarith
  have er41 : r c 4 1 = 1/12 := by nlinarith
  have er51 : r c 5 1 = 1/12 := by nlinarith
  exact ⟨er20, er30, er40, er50, er21, er31, er41, er51⟩

/-- Degree saturation in the two-point branch: every active--inactive edge
has squared magnitude `1/12`, and in particular the inactive edge `23`
vanishes. -/
lemma twoSupport01_edges (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (hs : TwoSupport01 c) :
    TwoSupport01Edges c := by
  rcases twoSupport01_magnitudes c d hc hd hnc hnd hdist hs with
    ⟨hr20, hr30, hr40, hr50, hr21, hr31, hr41, hr51⟩
  have hr02 : r c 0 2 = 1/12 := (r_symm c 0 2).trans hr20
  have hr03 : r c 0 3 = 1/12 := (r_symm c 0 3).trans hr30
  have hr04 : r c 0 4 = 1/12 := (r_symm c 0 4).trans hr40
  have hr05 : r c 0 5 = 1/12 := (r_symm c 0 5).trans hr50
  have hr12 : r c 1 2 = 1/12 := (r_symm c 1 2).trans hr21
  have hr13 : r c 1 3 = 1/12 := (r_symm c 1 3).trans hr31
  have hr14 : r c 1 4 = 1/12 := (r_symm c 1 4).trans hr41
  have hr15 : r c 1 5 = 1/12 := (r_symm c 1 5).trans hr51
  have hR2 := (pq_degree c d hc hd hnc hnd hdist 2).2.1
  rw [Rdeg2, hs.p2_zero, r_symm c 2 0, r_symm c 2 1, hr02, hr12] at hR2
  have hr23 : r c 2 3 = 0 := by
    nlinarith [r_nonneg c 2 3, r_nonneg c 2 4, r_nonneg c 2 5]
  have hd23sq : Complex.normSq (damp c 2 3) = 0 := by
    rw [normSq_damp_eq_r c 2 3 (by decide), hr23]
  have hd23 : damp c 2 3 = 0 := Complex.normSq_eq_zero.mp hd23sq
  exact ⟨hr02, hr03, hr04, hr05, hr12, hr13, hr14, hr15, hd23⟩

private lemma yamp_ne_zero_of_p_pos (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (i : Fin 6) (hi : 0 < p c i) :
    yamp d i ≠ 0 := by
  have hpq := (pq_degree c d hc hd hnc hnd hdist i).1
  have hq : 0 < q d i := by nlinarith
  exact Complex.normSq_pos.mp (by simpa only [q, yamp] using hq)

private lemma damp_ne_zero_of_r_eq (c : SS.State 6 ℂ) (i j : Fin 6)
    (hij : i ≠ j) (hr : r c i j = 1/12) : damp c i j ≠ 0 := by
  apply Complex.normSq_pos.mp
  rw [normSq_damp_eq_r c i j hij, hr]
  norm_num

/-- The pair-flip row forces opposite endpoint phase ratios in the
two-active-vertex branch.  This is proved without choosing local phases. -/
lemma twoSupport01_rho_anti (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (hs : TwoSupport01 c) :
    rho c d 0 + rho c d 1 = 0 := by
  rcases twoSupport01_probabilities c d hc hd hnc hnd hdist hs with
    ⟨hp0, hp1, hab⟩
  have he := twoSupport01_edges c d hc hd hnc hnd hdist hs
  have hc13 := camp_eq_rho_mul_star_damp c d hc hd hdist 3 1 (by decide) hs.p1_pos
  have hc02 := camp_eq_rho_mul_star_damp c d hc hd hdist 2 0 (by decide) hs.p0_pos
  have hc03 := camp_eq_rho_mul_star_damp c d hc hd hdist 3 0 (by decide) hs.p0_pos
  have hc12 := camp_eq_rho_mul_star_damp c d hc hd hdist 2 1 (by decide) hs.p1_pos
  rw [camp_symm d 3 1, damp_symm c 3 1] at hc13
  rw [camp_symm d 2 0, damp_symm c 2 0] at hc02
  rw [camp_symm d 3 0, damp_symm c 3 0] at hc03
  rw [camp_symm d 2 1, damp_symm c 2 1] at hc12
  have hpair := (pair_rows c d hc hd hdist).h0123
  have hpair' :
      star (damp c 0 2) * camp d 1 3 +
      star (damp c 1 3) * camp d 0 2 +
      star (damp c 0 3) * camp d 1 2 +
      star (damp c 1 2) * camp d 0 3 = 0 := by
    simpa [pairRow, hab, he.damp23_zero] using hpair
  rw [hc13, hc02, hc12, hc03] at hpair'
  let A : ℂ := star (damp c 0 2) * star (damp c 1 3) +
    star (damp c 0 3) * star (damp c 1 2)
  have hfactor : (rho c d 0 + rho c d 1) * A = 0 := by
    dsimp [A]
    simp only [Complex.star_def] at hpair' ⊢
    linear_combination hpair'
  have hpq2 := (pq_degree c d hc hd hnc hnd hdist 2).1
  have hpq3 := (pq_degree c d hc hd hnc hnd hdist 3).1
  have hpq4 := (pq_degree c d hc hd hnc hnd hdist 4).1
  have hpq5 := (pq_degree c d hc hd hnc hnd hdist 5).1
  have hy2 : yamp d 2 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq2.symm.trans hs.p2_zero
  have hy3 : yamp d 3 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq3.symm.trans hs.p3_zero
  have hy4 : yamp d 4 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq4.symm.trans hs.p4_zero
  have hy5 : yamp d 5 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq5.symm.trans hs.p5_zero
  have hb2 := companion2_explicit c d hc hd hdist
  have hb3 := companion3_explicit c d hc hd hdist
  simp only [hy2, hy3, hy4, hy5] at hb2 hb3
  have hb2' : damp c 2 0 * star (yamp d 0) +
      damp c 2 1 * star (yamp d 1) = 0 := by simpa using hb2
  have hb3' : damp c 3 0 * star (yamp d 0) +
      damp c 3 1 * star (yamp d 1) = 0 := by simpa using hb3
  have hb2s : star (damp c 2 0) * yamp d 0 +
      star (damp c 2 1) * yamp d 1 = 0 := by
    have h := congrArg star hb2'
    simpa [map_add, map_mul] using h
  have hb3s : star (damp c 3 0) * yamp d 0 +
      star (damp c 3 1) * yamp d 1 = 0 := by
    have h := congrArg star hb3'
    simpa [map_add, map_mul] using h
  have hA : A ≠ 0 := by
    intro hz
    have hz' : star (damp c 2 0) * star (damp c 3 1) +
        star (damp c 3 0) * star (damp c 2 1) = 0 := by
      dsimp [A] at hz
      simpa [damp_symm] using hz
    have hprod : (2 : ℂ) * star (damp c 2 0) *
        star (damp c 3 0) * yamp d 0 = 0 := by
      linear_combination
        star (damp c 2 0) * hb3s + star (damp c 3 0) * hb2s -
          yamp d 1 * hz'
    have hd20 : damp c 2 0 ≠ 0 :=
      damp_ne_zero_of_r_eq c 2 0 (by decide) ((r_symm c 2 0).trans he.r02)
    have hd30 : damp c 3 0 ≠ 0 :=
      damp_ne_zero_of_r_eq c 3 0 (by decide) ((r_symm c 3 0).trans he.r03)
    have hy0 := yamp_ne_zero_of_p_pos c d hc hd hnc hnd hdist 0 hs.p0_pos
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (star_ne_zero.mpr hd20)) (star_ne_zero.mpr hd30)) hy0) hprod
  exact (mul_eq_zero.mp hfactor).resolve_right hA

private lemma rho_normSq_one (R x y : ℂ)
    (hx : Complex.normSq x = 1/6) (hy : Complex.normSq y = 1/6)
    (hR : R * star x = y) : Complex.normSq R = 1 := by
  have h := congrArg Complex.normSq hR
  rw [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj, hx, hy] at h
  nlinarith

private lemma edge_phase_of_companion (R0 R1 x0 x1 y0 y1 d0 d1 : ℂ)
    (hy0 : R0 * star x0 = y0) (hy1 : R1 * star x1 = y1)
    (hanti : R0 + R1 = 0) (hR0 : R0 ≠ 0)
    (hrow : d0 * star y0 + d1 * star y1 = 0) :
    d0 * x0 = d1 * x1 := by
  have hR1 : R1 = -R0 := by linear_combination hanti
  rw [← hy0, ← hy1, hR1] at hrow
  simp only [star_mul', star_neg, star_star] at hrow
  have hfac : star R0 * (d0 * x0 - d1 * x1) = 0 := by
    linear_combination hrow
  have hz := (mul_eq_zero.mp hfac).resolve_left (star_ne_zero.mpr hR0)
  linear_combination hz

private lemma c_cross_expectation (x0 x1 d0 d1 : ℂ)
    (hx1 : Complex.normSq x1 = 1/6)
    (hd0 : Complex.normSq d0 = 1/12)
    (hphase : d0 * x0 = d1 * x1) :
    star d1 * d0 = (1/2 : ℂ) * (star x0 * x1) := by
  have hs := congrArg star hphase
  simp only [star_mul'] at hs
  have hm : (star d0 * d0) * (star x0 * x1) =
      (star d1 * d0) * (star x1 * x1) := by
    calc
      (star d0 * d0) * (star x0 * x1) =
          (star d0 * star x0) * (d0 * x1) := by ring
      _ = (star d1 * star x1) * (d0 * x1) := by rw [hs]
      _ = (star d1 * d0) * (star x1 * x1) := by ring
  rw [SixQubit.CodeEquiv.star_mul_self, SixQubit.CodeEquiv.star_mul_self,
    hd0, hx1] at hm
  calc
    star d1 * d0 = 6 * ((star d1 * d0) * ((1/6 : ℝ) : ℂ)) := by norm_num; ring
    _ = 6 * (((1/12 : ℝ) : ℂ) * (star x0 * x1)) := by rw [← hm]
    _ = (1/2 : ℂ) * (star x0 * x1) := by norm_num; ring

private lemma d_singleton_expectation (R0 R1 x0 x1 y0 y1 : ℂ)
    (hy0 : R0 * star x0 = y0) (hy1 : R1 * star x1 = y1)
    (hanti : R0 + R1 = 0) (hunit : star R0 * R0 = 1) :
    star y1 * y0 = -(star x0 * x1) := by
  have hR1 : R1 = -R0 := by linear_combination hanti
  rw [← hy0, ← hy1, hR1]
  simp only [star_mul', star_neg, star_star]
  calc
    (-star R0 * x1) * (R0 * star x0) =
        -(star R0 * R0) * (star x0 * x1) := by ring
    _ = -(star x0 * x1) := by rw [hunit]; ring

private lemma d_cross_expectation (R0 R1 d0 d1 e0 e1 : ℂ)
    (he0 : e0 = R0 * star d0) (he1 : e1 = R1 * star d1)
    (hanti : R0 + R1 = 0) (hunit : star R0 * R0 = 1) :
    star e0 * e1 = -(star d1 * d0) := by
  have hR1 : R1 = -R0 := by linear_combination hanti
  rw [he0, he1, hR1]
  simp only [star_mul', star_star]
  calc
    (star R0 * d0) * (-R0 * star d1) =
        -(star R0 * R0) * (star d1 * d0) := by ring
    _ = -(star d1 * d0) := by rw [hunit]; ring

private lemma rho_mul_star_xamp_local (c d : SS.State 6 ℂ) (i : Fin 6)
    (hi : 0 < p c i) :
    rho c d i * star (xamp c i) = yamp d i := by
  unfold rho
  exact div_mul_cancel₀ _ (star_ne_zero.mpr (xamp_ne_zero_of_p_pos c i hi))

/-- A genuine full-fibre orbit-9 code cannot have exactly the two active
singleton coordinates `0,1`.  The contradiction is the diagonal KL row for
the detectable hop `sigma_0^+ sigma_1^-`. -/
theorem twoSupport01_impossible (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (hs : TwoSupport01 c) : False := by
  rcases twoSupport01_probabilities c d hc hd hnc hnd hdist hs with
    ⟨hp0, hp1, _⟩
  have he := twoSupport01_edges c d hc hd hnc hnd hdist hs
  have hanti := twoSupport01_rho_anti c d hc hd hnc hnd hdist hs
  have hyR0 := rho_mul_star_xamp_local c d 0 hs.p0_pos
  have hyR1 := rho_mul_star_xamp_local c d 1 hs.p1_pos
  have hx0sq : Complex.normSq (xamp c 0) = 1/6 := by
    simpa [p, xamp] using hp0
  have hx1sq : Complex.normSq (xamp c 1) = 1/6 := by
    simpa [p, xamp] using hp1
  have hpq0 := (pq_degree c d hc hd hnc hnd hdist 0).1
  have hpq1 := (pq_degree c d hc hd hnc hnd hdist 1).1
  have hy0sq : Complex.normSq (yamp d 0) = 1/6 := by
    have hq0 : q d 0 = 1/6 := hpq0.symm.trans hp0
    simpa only [q, yamp] using hq0
  have hy1sq : Complex.normSq (yamp d 1) = 1/6 := by
    have hq1 : q d 1 = 1/6 := hpq1.symm.trans hp1
    simpa only [q, yamp] using hq1
  have hrhoSq : Complex.normSq (rho c d 0) = 1 :=
    rho_normSq_one _ _ _ hx0sq hy0sq hyR0
  have hunit : star (rho c d 0) * rho c d 0 = 1 := by
    rw [SixQubit.CodeEquiv.star_mul_self, hrhoSq]
    norm_num
  have hy0ne : yamp d 0 ≠ 0 :=
    yamp_ne_zero_of_p_pos c d hc hd hnc hnd hdist 0 hs.p0_pos
  have hrho0ne : rho c d 0 ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hyR0
    exact hy0ne hyR0.symm
  have hpq2 := (pq_degree c d hc hd hnc hnd hdist 2).1
  have hpq3 := (pq_degree c d hc hd hnc hnd hdist 3).1
  have hpq4 := (pq_degree c d hc hd hnc hnd hdist 4).1
  have hpq5 := (pq_degree c d hc hd hnc hnd hdist 5).1
  have hy2 : yamp d 2 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq2.symm.trans hs.p2_zero
  have hy3 : yamp d 3 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq3.symm.trans hs.p3_zero
  have hy4 : yamp d 4 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq4.symm.trans hs.p4_zero
  have hy5 : yamp d 5 = 0 := by
    apply Complex.normSq_eq_zero.mp
    simpa [q, yamp] using hpq5.symm.trans hs.p5_zero
  have hb2 := companion2_explicit c d hc hd hdist
  have hb3 := companion3_explicit c d hc hd hdist
  have hb4 := companion4_explicit c d hc hd hdist
  have hb5 := companion5_explicit c d hc hd hdist
  simp only [hy2, hy3, hy4, hy5] at hb2 hb3 hb4 hb5
  have hb2' : damp c 0 2 * star (yamp d 0) +
      damp c 1 2 * star (yamp d 1) = 0 := by
    simpa [damp_symm] using hb2
  have hb3' : damp c 0 3 * star (yamp d 0) +
      damp c 1 3 * star (yamp d 1) = 0 := by
    simpa [damp_symm] using hb3
  have hb4' : damp c 0 4 * star (yamp d 0) +
      damp c 1 4 * star (yamp d 1) = 0 := by
    simpa [damp_symm] using hb4
  have hb5' : damp c 0 5 * star (yamp d 0) +
      damp c 1 5 * star (yamp d 1) = 0 := by
    simpa [damp_symm] using hb5
  have hph2 := edge_phase_of_companion _ _ _ _ _ _ _ _
    hyR0 hyR1 hanti hrho0ne hb2'
  have hph3 := edge_phase_of_companion _ _ _ _ _ _ _ _
    hyR0 hyR1 hanti hrho0ne hb3'
  have hph4 := edge_phase_of_companion _ _ _ _ _ _ _ _
    hyR0 hyR1 hanti hrho0ne hb4'
  have hph5 := edge_phase_of_companion _ _ _ _ _ _ _ _
    hyR0 hyR1 hanti hrho0ne hb5'
  have hd02sq : Complex.normSq (damp c 0 2) = 1/12 := by
    rw [normSq_damp_eq_r c 0 2 (by decide), he.r02]
  have hd03sq : Complex.normSq (damp c 0 3) = 1/12 := by
    rw [normSq_damp_eq_r c 0 3 (by decide), he.r03]
  have hd04sq : Complex.normSq (damp c 0 4) = 1/12 := by
    rw [normSq_damp_eq_r c 0 4 (by decide), he.r04]
  have hd05sq : Complex.normSq (damp c 0 5) = 1/12 := by
    rw [normSq_damp_eq_r c 0 5 (by decide), he.r05]
  have hc2 := c_cross_expectation (xamp c 0) (xamp c 1)
    (damp c 0 2) (damp c 1 2) hx1sq hd02sq hph2
  have hc3 := c_cross_expectation (xamp c 0) (xamp c 1)
    (damp c 0 3) (damp c 1 3) hx1sq hd03sq hph3
  have hc4 := c_cross_expectation (xamp c 0) (xamp c 1)
    (damp c 0 4) (damp c 1 4) hx1sq hd04sq hph4
  have hc5 := c_cross_expectation (xamp c 0) (xamp c 1)
    (damp c 0 5) (damp c 1 5) hx1sq hd05sq hph5
  have hcamp02 := camp_eq_rho_mul_star_damp c d hc hd hdist 2 0 (by decide) hs.p0_pos
  have hcamp12 := camp_eq_rho_mul_star_damp c d hc hd hdist 2 1 (by decide) hs.p1_pos
  have hcamp03 := camp_eq_rho_mul_star_damp c d hc hd hdist 3 0 (by decide) hs.p0_pos
  have hcamp13 := camp_eq_rho_mul_star_damp c d hc hd hdist 3 1 (by decide) hs.p1_pos
  have hcamp04 := camp_eq_rho_mul_star_damp c d hc hd hdist 4 0 (by decide) hs.p0_pos
  have hcamp14 := camp_eq_rho_mul_star_damp c d hc hd hdist 4 1 (by decide) hs.p1_pos
  have hcamp05 := camp_eq_rho_mul_star_damp c d hc hd hdist 5 0 (by decide) hs.p0_pos
  have hcamp15 := camp_eq_rho_mul_star_damp c d hc hd hdist 5 1 (by decide) hs.p1_pos
  rw [camp_symm d 2 0, damp_symm c 2 0] at hcamp02
  rw [camp_symm d 2 1, damp_symm c 2 1] at hcamp12
  rw [camp_symm d 3 0, damp_symm c 3 0] at hcamp03
  rw [camp_symm d 3 1, damp_symm c 3 1] at hcamp13
  rw [camp_symm d 4 0, damp_symm c 4 0] at hcamp04
  rw [camp_symm d 4 1, damp_symm c 4 1] at hcamp14
  rw [camp_symm d 5 0, damp_symm c 5 0] at hcamp05
  rw [camp_symm d 5 1, damp_symm c 5 1] at hcamp15
  have hdS := d_singleton_expectation _ _ _ _ _ _ hyR0 hyR1 hanti hunit
  have hd2 := d_cross_expectation _ _ _ _ _ _ hcamp02 hcamp12 hanti hunit
  have hd3 := d_cross_expectation _ _ _ _ _ _ hcamp03 hcamp13 hanti hunit
  have hd4 := d_cross_expectation _ _ _ _ _ _ hcamp04 hcamp14 hanti hunit
  have hd5 := d_cross_expectation _ _ _ _ _ _ hcamp05 hcamp15 hanti hunit
  have hkl := SixQubit.Orbit8Universal.inner_rl_eq c d hnc hnd hdist 0 1
  rw [SixQubit.Orbit8Universal.rl_ne 0 1 (by decide) c,
    SixQubit.Orbit8Universal.rl_ne 0 1 (by decide) d,
    inner_hop01_S0 c hc, inner_hop01_S1 d hd] at hkl
  rw [hc2, hc3, hc4, hc5, hdS, hd2, hd3, hd4, hd5,
    hc2, hc3, hc4, hc5] at hkl
  have hbase : star (xamp c 0) * xamp c 1 = 0 := by
    ring_nf at hkl
    linear_combination (1/6) * hkl
  exact (mul_ne_zero (star_ne_zero.mpr (xamp_ne_zero_of_p_pos c 0 hs.p0_pos))
    (xamp_ne_zero_of_p_pos c 1 hs.p1_pos)) hbase

end

end SixQubit.Orbit9Universal
