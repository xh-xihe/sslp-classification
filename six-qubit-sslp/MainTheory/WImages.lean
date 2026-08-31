import Mathlib
import MainTheory.Levels
import SixQubit.Orbit10Enum
import SixQubit.Orbit11Enum
import SixQubit.Orbit16Enum
import SixQubit.Orbit22Enum
import SixQubit.Orbit23Enum
import SixQubit.Orbit9UniversalFinal
import SixQubit.Orbit7UniversalFinal
import SixQubit.Orbit8UniversalFinal
import SixQubit.Orbit45Final
import SixQubit.Orbit9Attain

/-!
# Weight-enumerator images, orbit by orbit

`MainTheory/Levels.lean` defines level (iii) of `main.tex` Definition 6.1, the
weight-enumerator image `W_r` of an SSLP moment orbit.  This file evaluates it
for the orbits whose image the six-qubit development pins to a single point,
restating those results in the paper's own terminology.

Each proof is two inclusions: the uniqueness half of the orbit's
`enumerator_pair_unique_fiber` gives the forward one, and the exhibited code of
`Orbit<n>Real` gives the reverse.  All the mathematics was already done in
`SixQubit/`; what is new is that `main.tex`'s `W_r` is a Lean object those
results are about.

The one-parameter images of orbits 7, 8 and 45 are stated below as images of
closed intervals.  Their two-sided raw-enumerator characterizations come from
`SixQubit/Orbit7UniversalFinal.lean` and companions.  The singleton statements
for orbits 9 and 21 come from their corresponding `fully_certified` results
(orbit 21's paper-facing wrapper is in `MainTheory/Levels.lean`).
-/

namespace MainTheory.WImages

open SS.MacWilliams

/-- The normalized enumerator
`E_1^A = (1,1,0,0,15,15,0)` of `main.tex`. -/
def E1A : Fin 7 → ℝ := ![1, 1, 0, 0, 15, 15, 0]

set_option maxRecDepth 20000 in
/-- **Orbit 10's weight-enumerator image is a single point.** -/
theorem WImage_orbit10 :
    Levels.WImage SixQubit.Orbit10Real.av 0 2 = {Levels.E2A} := by
  classical
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
      (SixQubit.Orbit10Enum.enumerator_pair_unique_fiber c d hc hd hnc hnd hdist).1
    funext j
    fin_cases j <;> simp [Levels.E2A, hA, h0, h1, h2, h3, h4, h5, h6] <;> norm_num
  · intro hA
    have hs0 : ∀ s, SS.weight SixQubit.Orbit10Real.av s ≠ 0 →
        SixQubit.Orbit10Real.w0 s = 0 := by
      intro s hs
      refine SixQubit.Orbit10Real.w0_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit10Enum.L0_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    have hs1 : ∀ s, SS.weight SixQubit.Orbit10Real.av s ≠ 2 →
        SixQubit.Orbit10Real.w1 s = 0 := by
      intro s hs
      refine SixQubit.Orbit10Real.w1_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit10Enum.L1_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := (SixQubit.Orbit10Enum.enumerator_pair_attained).1
    refine ⟨SixQubit.Orbit10Real.w0, SixQubit.Orbit10Real.w1, hs0, hs1,
      SixQubit.Orbit10Real.w0_normalized, SixQubit.Orbit10Real.w1_normalized,
      SixQubit.Orbit10Real.is_code, fun j => ?_⟩
    have hAE : A = Levels.E2A := hA
    subst hAE
    fin_cases j <;> simp [Levels.E2A, h0, h1, h2, h3, h4, h5, h6] <;> norm_num

set_option maxRecDepth 20000 in
/-- **Orbit 11's weight-enumerator image is a single point.** -/
theorem WImage_orbit11 :
    Levels.WImage SixQubit.Orbit11Real.av 0 2 = {E1A} := by
  classical
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
      (SixQubit.Orbit11Enum.enumerator_pair_unique_fiber c d hc hd hnc hnd hdist).1
    funext j
    fin_cases j <;> simp [E1A, hA, h0, h1, h2, h3, h4, h5, h6] <;> norm_num
  · intro hA
    have hs0 : ∀ s, SS.weight SixQubit.Orbit11Real.av s ≠ 0 →
        SixQubit.Orbit11Real.w0 s = 0 := by
      intro s hs
      refine SixQubit.Orbit11Real.w0_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit11Enum.L0_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    have hs1 : ∀ s, SS.weight SixQubit.Orbit11Real.av s ≠ 2 →
        SixQubit.Orbit11Real.w1 s = 0 := by
      intro s hs
      refine SixQubit.Orbit11Real.w1_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit11Enum.L1_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := (SixQubit.Orbit11Enum.enumerator_pair_attained).1
    refine ⟨SixQubit.Orbit11Real.w0, SixQubit.Orbit11Real.w1, hs0, hs1,
      SixQubit.Orbit11Real.w0_normalized, SixQubit.Orbit11Real.w1_normalized,
      SixQubit.Orbit11Real.is_code, fun j => ?_⟩
    have hAE : A = E1A := hA
    subst hAE
    fin_cases j <;> simp [E1A, h0, h1, h2, h3, h4, h5, h6] <;> norm_num

set_option maxRecDepth 20000 in
/-- **Orbit 16's weight-enumerator image is a single point.** -/
theorem WImage_orbit16 :
    Levels.WImage SixQubit.Orbit16Real.av 0 2 = {Levels.E2A} := by
  classical
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
      (SixQubit.Orbit16Enum.enumerator_pair_unique_fiber c d hc hd hnc hnd hdist).1
    funext j
    fin_cases j <;> simp [Levels.E2A, hA, h0, h1, h2, h3, h4, h5, h6] <;> norm_num
  · intro hA
    have hs0 : ∀ s, SS.weight SixQubit.Orbit16Real.av s ≠ 0 →
        SixQubit.Orbit16Real.w0 s = 0 := by
      intro s hs
      refine SixQubit.Orbit16Real.w0_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit16Enum.L0_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    have hs1 : ∀ s, SS.weight SixQubit.Orbit16Real.av s ≠ 2 →
        SixQubit.Orbit16Real.w1 s = 0 := by
      intro s hs
      refine SixQubit.Orbit16Real.w1_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit16Enum.L1_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := (SixQubit.Orbit16Enum.enumerator_pair_attained).1
    refine ⟨SixQubit.Orbit16Real.w0, SixQubit.Orbit16Real.w1, hs0, hs1,
      SixQubit.Orbit16Real.w0_normalized, SixQubit.Orbit16Real.w1_normalized,
      SixQubit.Orbit16Real.is_code, fun j => ?_⟩
    have hAE : A = Levels.E2A := hA
    subst hAE
    fin_cases j <;> simp [Levels.E2A, h0, h1, h2, h3, h4, h5, h6] <;> norm_num

set_option maxRecDepth 20000 in
/-- **Orbit 22's weight-enumerator image is a single point.** -/
theorem WImage_orbit22 :
    Levels.WImage SixQubit.Orbit22Real.av 0 2 = {Levels.E2A} := by
  classical
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
      (SixQubit.Orbit22Enum.enumerator_pair_unique_fiber c d hc hd hnc hnd hdist).1
    funext j
    fin_cases j <;> simp [Levels.E2A, hA, h0, h1, h2, h3, h4, h5, h6] <;> norm_num
  · intro hA
    have hs0 : ∀ s, SS.weight SixQubit.Orbit22Real.av s ≠ 0 →
        SixQubit.Orbit22Real.w0 s = 0 := by
      intro s hs
      refine SixQubit.Orbit22Real.w0_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit22Enum.L0_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    have hs1 : ∀ s, SS.weight SixQubit.Orbit22Real.av s ≠ 2 →
        SixQubit.Orbit22Real.w1 s = 0 := by
      intro s hs
      refine SixQubit.Orbit22Real.w1_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit22Enum.L1_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := (SixQubit.Orbit22Enum.enumerator_pair_attained).1
    refine ⟨SixQubit.Orbit22Real.w0, SixQubit.Orbit22Real.w1, hs0, hs1,
      SixQubit.Orbit22Real.w0_normalized, SixQubit.Orbit22Real.w1_normalized,
      SixQubit.Orbit22Real.is_code, fun j => ?_⟩
    have hAE : A = Levels.E2A := hA
    subst hAE
    fin_cases j <;> simp [Levels.E2A, h0, h1, h2, h3, h4, h5, h6] <;> norm_num

set_option maxRecDepth 20000 in
/-- **Orbit 23's weight-enumerator image is a single point.** -/
theorem WImage_orbit23 :
    Levels.WImage SixQubit.Orbit23Real.av 0 2 = {E1A} := by
  classical
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
      (SixQubit.Orbit23Enum.enumerator_pair_unique_fiber c d hc hd hnc hnd hdist).1
    funext j
    fin_cases j <;> simp [E1A, hA, h0, h1, h2, h3, h4, h5, h6] <;> norm_num
  · intro hA
    have hs0 : ∀ s, SS.weight SixQubit.Orbit23Real.av s ≠ 0 →
        SixQubit.Orbit23Real.w0 s = 0 := by
      intro s hs
      refine SixQubit.Orbit23Real.w0_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit23Enum.L0_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    have hs1 : ∀ s, SS.weight SixQubit.Orbit23Real.av s ≠ 2 →
        SixQubit.Orbit23Real.w1 s = 0 := by
      intro s hs
      refine SixQubit.Orbit23Real.w1_vanishes s (fun hmem => hs ?_)
      have hm := List.mem_toFinset.mpr hmem
      rw [← SixQubit.Orbit23Enum.L1_eq_fiber] at hm
      exact (Finset.mem_filter.mp hm).2
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := (SixQubit.Orbit23Enum.enumerator_pair_attained).1
    refine ⟨SixQubit.Orbit23Real.w0, SixQubit.Orbit23Real.w1, hs0, hs1,
      SixQubit.Orbit23Real.w0_normalized, SixQubit.Orbit23Real.w1_normalized,
      SixQubit.Orbit23Real.is_code, fun j => ?_⟩
    have hAE : A = E1A := hA
    subst hAE
    fin_cases j <;> simp [E1A, h0, h1, h2, h3, h4, h5, h6] <;> norm_num

/-- **Orbit 9's weight-enumerator image is a single point.**

Both halves come from `Orbit9Universal.fully_kernel_certified`, whose
support-reduction argument is what makes the uniqueness half apply to the whole
fiber rather than to the exhibited support. -/
theorem WImage_orbit9 :
    Levels.WImage SixQubit.Orbit9Real.av 0 1 = {Levels.E2A} := by
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ :=
      (SixQubit.Orbit9Universal.fully_kernel_certified.1 c d hc hd hnc hnd hdist).1.1
    funext j
    fin_cases j <;> simp [Levels.E2A, hA, h0, h1, h2, h3, h4, h5, h6] <;> norm_num
  · intro hA
    obtain ⟨c, d, hc, hd, hnc, hnd, hdist, hE, _⟩ :=
      SixQubit.Orbit9Universal.fully_kernel_certified.2
    refine ⟨c, d, hc, hd, hnc, hnd, hdist, fun j => ?_⟩
    have hAE : A = Levels.E2A := hA
    subst hAE
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hE
    fin_cases j <;> simp [Levels.E2A, h0, h1, h2, h3, h4, h5, h6] <;> norm_num

/-! ## Orbits with a one-parameter image

Orbits 7, 8 and 45 have `W_r` an interval rather than a point, so the statement
is an image of a `Set.Icc` under the family map rather than a singleton.  Both
inclusions again come from the orbit's `fully_certified`: the converse half
gives that every code lands in the family, the attainment half that every
parameter is realized. -/

/-- The normalized family `F_I(a)=\mathcal L(a)` of `main.tex`. -/
def FI (a : ℝ) : Fin 7 → ℝ :=
  ![1, a, 1-a, 0, 11+4*a, 16-a, 3-3*a]

/-- The normalized family `F_II(t)` of `main.tex`. -/
def FII (t : ℝ) : Fin 7 → ℝ :=
  ![1, 0, t, 1-t, 12-t, 15+t, 3]

set_option maxRecDepth 20000 in
/-- **Orbit 7's weight-enumerator image is the whole interval family.** -/
theorem WImage_orbit7 :
    Levels.WImage SixQubit.Orbit7Real.av 0 1 = FI '' Set.Icc 0 1 := by
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    obtain ⟨a, ha0, ha1, hFA, _, _⟩ :=
      SixQubit.Orbit7Universal.fully_certified.1 c d hc hd hnc hnd hdist
    refine ⟨a, Set.mem_Icc.2 ⟨ha0, ha1⟩, ?_⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hFA
    funext j
    fin_cases j <;> simp [FI, hA, h0, h1, h2, h3, h4, h5, h6]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ha0, ha1⟩ := Set.mem_Icc.1 ha
    obtain ⟨C, S, _, _, hnorm, hdist, hv0, hv1, hFA, _, _⟩ :=
      SixQubit.Orbit7Universal.fully_certified.2 a ha0 ha1
    refine ⟨SixQubit.Orbit7Family.w0 C S, SixQubit.Orbit7Family.w1 C S,
      hv0, hv1, hnorm 0, hnorm 1, hdist, fun j => ?_⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hFA
    simp only [SixQubit.Orbit7Family.code] at h0 h1 h2 h3 h4 h5 h6
    fin_cases j <;> simp [FI, h0, h1, h2, h3, h4, h5, h6]

set_option maxRecDepth 20000 in
/-- **Orbit 8's weight-enumerator image is the upper half of the same family.** -/
theorem WImage_orbit8 :
    Levels.WImage SixQubit.Orbit8Real.av 0 1 = FI '' Set.Icc (1/2) 1 := by
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    obtain ⟨a, ha0, ha1, hFA, _⟩ :=
      SixQubit.Orbit8Universal.fully_certified.1 c d hc hd hnc hnd hdist
    refine ⟨a, Set.mem_Icc.2 ⟨ha0, ha1⟩, ?_⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hFA
    funext j
    fin_cases j <;> simp [FI, hA, h0, h1, h2, h3, h4, h5, h6]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ha0, ha1⟩ := Set.mem_Icc.1 ha
    obtain ⟨C, S, _, _, hnorm, hdist, hv0, hv1, hFA, _⟩ :=
      SixQubit.Orbit8Universal.fully_certified.2 a ha0 ha1
    refine ⟨SixQubit.Orbit8Family.w0 C S, SixQubit.Orbit8Family.w1 C S,
      hv0, hv1, hnorm 0, hnorm 1, hdist, fun j => ?_⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hFA
    simp only [SixQubit.Orbit8Family.code] at h0 h1 h2 h3 h4 h5 h6
    fin_cases j <;> simp [FI, h0, h1, h2, h3, h4, h5, h6]

set_option maxRecDepth 20000 in
/-- **Orbit 45's weight-enumerator image is the interval family `F_II`.** -/
theorem WImage_orbit45 :
    Levels.WImage SixQubit.Orbit45Support.av 0 3 = FII '' Set.Icc (2/3) 1 := by
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    obtain ⟨t, ht0, ht1, hFA, _⟩ :=
      SixQubit.Orbit45Final.fully_certified.1 c d hc hd hnc hnd hdist
    refine ⟨t, Set.mem_Icc.2 ⟨ht0, ht1⟩, ?_⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hFA
    funext j
    fin_cases j <;> simp [FII, hA, h0, h1, h2, h3, h4, h5, h6]
    all_goals norm_num
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨ht0, ht1⟩ := Set.mem_Icc.1 ht
    obtain ⟨c, d, hc, hd, hnc, hnd, hdist, hFA, _⟩ :=
      SixQubit.Orbit45Final.fully_certified.2 t ht0 ht1
    refine ⟨c, d, hc, hd, hnc, hnd, hdist, fun j => ?_⟩
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hFA
    fin_cases j <;> simp [FII, h0, h1, h2, h3, h4, h5, h6]
    all_goals norm_num

end MainTheory.WImages
