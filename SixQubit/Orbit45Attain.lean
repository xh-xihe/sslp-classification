import Mathlib

import SixQubit.Orbit45Family

/-!
# Orbit 45: explicit full-fibre interval attainment

The codewords below are written directly on the two complete fibres.  Thus the
construction does not appeal to an unformalized orthogonal completion.
-/

namespace SixQubit.Orbit45Attain

open scoped BigOperators ComplexConjugate
open SixQubit.Realize
open SixQubit.Orbit45Support
open SixQubit.Orbit45Universal
open SixQubit.Orbit45Family

noncomputable section

set_option maxRecDepth 20000

def phase (u v : ℝ) : ℂ := (u : ℂ) + (v : ℂ) * Complex.I

@[simp] theorem phase_re (u v : ℝ) : (phase u v).re = u := by
  simp [phase]

@[simp] theorem phase_im (u v : ℝ) : (phase u v).im = v := by
  simp [phase]

@[simp] theorem star_phase (u v : ℝ) : star (phase u v) = phase u (-v) := by
  apply Complex.ext <;> simp

theorem normSq_phase (u v : ℝ) :
    Complex.normSq (phase u v) = u^2 + v^2 := by
  simp [Complex.normSq_apply]
  ring

structure Params
    (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) : Prop where
  amp_sum : a1^2 + a2^2 + a3^2 = 1/4
  q_sq : q^2 = 1/8
  unit1 : u1^2 + v1^2 = 1
  unit2 : u2^2 + v2^2 = 1
  unit3 : u3^2 + v3^2 = 1
  triangle_re : u1*a1^2 + u2*a2^2 + u3*a3^2 = 0
  triangle_im : v1*a1^2 + v2*a2^2 + v3*a3^2 = 0

def cword (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) : SS.State 6 ℂ :=
  fun x =>
    if x = x0 then (a1 : ℂ)
    else if x = x1 then -(phase u1 (-v1) * (a1 : ℂ))
    else if x = x2 then (a2 : ℂ)
    else if x = x3 then -(phase u2 (-v2) * (a2 : ℂ))
    else if x = x4 then (a3 : ℂ)
    else if x = x5 then -(phase u3 (-v3) * (a3 : ℂ))
    else if x = x6 then (q : ℂ)
    else if x = x7 then (q : ℂ)
    else if x = x8 then (q : ℂ)
    else if x = x9 then -(q : ℂ)
    else 0

def dword (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) : SS.State 6 ℂ :=
  fun x =>
    if x = y0 then phase u1 v1 * (a1 : ℂ)
    else if x = y1 then -(a1 : ℂ)
    else if x = y2 then phase u2 v2 * (a2 : ℂ)
    else if x = y3 then -(a2 : ℂ)
    else if x = y4 then phase u3 v3 * (a3 : ℂ)
    else if x = y5 then -(a3 : ℂ)
    else if x = y6 then (q : ℂ)
    else if x = y7 then (q : ℂ)
    else if x = y8 then -(q : ℂ)
    else if x = y9 then (q : ℂ)
    else 0

def code (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    Fin 2 → SS.State 6 ℂ :=
  ![cword a1 a2 a3 q u1 v1 u2 v2 u3 v3,
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3]

@[simp] theorem cword_x0 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x0 = a1 := by simp [cword]
@[simp] theorem cword_x1 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x1 = -(phase u1 (-v1) * a1) := by
  simp [cword, show x1 ≠ x0 from by decide]
@[simp] theorem cword_x2 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x2 = a2 := by
  simp [cword, show x2 ≠ x0 from by decide, show x2 ≠ x1 from by decide]
@[simp] theorem cword_x3 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x3 = -(phase u2 (-v2) * a2) := by
  simp [cword, show x3 ≠ x0 from by decide, show x3 ≠ x1 from by decide,
    show x3 ≠ x2 from by decide]
@[simp] theorem cword_x4 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x4 = a3 := by
  simp [cword, show x4 ≠ x0 from by decide, show x4 ≠ x1 from by decide,
    show x4 ≠ x2 from by decide, show x4 ≠ x3 from by decide]
@[simp] theorem cword_x5 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x5 = -(phase u3 (-v3) * a3) := by
  simp [cword, show x5 ≠ x0 from by decide, show x5 ≠ x1 from by decide,
    show x5 ≠ x2 from by decide, show x5 ≠ x3 from by decide,
    show x5 ≠ x4 from by decide]
@[simp] theorem cword_x6 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x6 = q := by
  simp [cword, show x6 ≠ x0 from by decide, show x6 ≠ x1 from by decide,
    show x6 ≠ x2 from by decide, show x6 ≠ x3 from by decide,
    show x6 ≠ x4 from by decide, show x6 ≠ x5 from by decide]
@[simp] theorem cword_x7 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x7 = q := by
  simp [cword, show x7 ≠ x0 from by decide, show x7 ≠ x1 from by decide,
    show x7 ≠ x2 from by decide, show x7 ≠ x3 from by decide,
    show x7 ≠ x4 from by decide, show x7 ≠ x5 from by decide,
    show x7 ≠ x6 from by decide]
@[simp] theorem cword_x8 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x8 = q := by
  simp [cword, show x8 ≠ x0 from by decide, show x8 ≠ x1 from by decide,
    show x8 ≠ x2 from by decide, show x8 ≠ x3 from by decide,
    show x8 ≠ x4 from by decide, show x8 ≠ x5 from by decide,
    show x8 ≠ x6 from by decide, show x8 ≠ x7 from by decide]
@[simp] theorem cword_x9 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x9 = -q := by
  simp [cword, show x9 ≠ x0 from by decide, show x9 ≠ x1 from by decide,
    show x9 ≠ x2 from by decide, show x9 ≠ x3 from by decide,
    show x9 ≠ x4 from by decide, show x9 ≠ x5 from by decide,
    show x9 ≠ x6 from by decide, show x9 ≠ x7 from by decide,
    show x9 ≠ x8 from by decide]

@[simp] theorem dword_y0 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y0 = phase u1 v1 * a1 := by simp [dword]
@[simp] theorem dword_y1 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y1 = -a1 := by
  simp [dword, show y1 ≠ y0 from by decide]
@[simp] theorem dword_y2 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y2 = phase u2 v2 * a2 := by
  simp [dword, show y2 ≠ y0 from by decide, show y2 ≠ y1 from by decide]
@[simp] theorem dword_y3 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y3 = -a2 := by
  simp [dword, show y3 ≠ y0 from by decide, show y3 ≠ y1 from by decide,
    show y3 ≠ y2 from by decide]
@[simp] theorem dword_y4 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y4 = phase u3 v3 * a3 := by
  simp [dword, show y4 ≠ y0 from by decide, show y4 ≠ y1 from by decide,
    show y4 ≠ y2 from by decide, show y4 ≠ y3 from by decide]
@[simp] theorem dword_y5 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y5 = -a3 := by
  simp [dword, show y5 ≠ y0 from by decide, show y5 ≠ y1 from by decide,
    show y5 ≠ y2 from by decide, show y5 ≠ y3 from by decide,
    show y5 ≠ y4 from by decide]
@[simp] theorem dword_y6 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y6 = q := by
  simp [dword, show y6 ≠ y0 from by decide, show y6 ≠ y1 from by decide,
    show y6 ≠ y2 from by decide, show y6 ≠ y3 from by decide,
    show y6 ≠ y4 from by decide, show y6 ≠ y5 from by decide]
@[simp] theorem dword_y7 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y7 = q := by
  simp [dword, show y7 ≠ y0 from by decide, show y7 ≠ y1 from by decide,
    show y7 ≠ y2 from by decide, show y7 ≠ y3 from by decide,
    show y7 ≠ y4 from by decide, show y7 ≠ y5 from by decide,
    show y7 ≠ y6 from by decide]
@[simp] theorem dword_y8 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y8 = -q := by
  simp [dword, show y8 ≠ y0 from by decide, show y8 ≠ y1 from by decide,
    show y8 ≠ y2 from by decide, show y8 ≠ y3 from by decide,
    show y8 ≠ y4 from by decide, show y8 ≠ y5 from by decide,
    show y8 ≠ y6 from by decide, show y8 ≠ y7 from by decide]
@[simp] theorem dword_y9 (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 y9 = q := by
  simp [dword, show y9 ≠ y0 from by decide, show y9 ≠ y1 from by decide,
    show y9 ≠ y2 from by decide, show y9 ≠ y3 from by decide,
    show y9 ≠ y4 from by decide, show y9 ≠ y5 from by decide,
    show y9 ≠ y6 from by decide, show y9 ≠ y7 from by decide,
    show y9 ≠ y8 from by decide]

theorem cword_support (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    ∀ x, x ∉ S0 → cword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x = 0 := by
  intro x hx
  simp only [S0, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  simp [cword, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
    hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.2.2.2]

theorem dword_support (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ) :
    ∀ x, x ∉ S1 → dword a1 a2 a3 q u1 v1 u2 v2 u3 v3 x = 0 := by
  intro x hx
  simp only [S1, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  simp [dword, hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
    hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.2.2.2]

theorem cword_normalized
    (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ)
    (hp : Params a1 a2 a3 q u1 v1 u2 v2 u3 v3) :
    SS.innerC (cword a1 a2 a3 q u1 v1 u2 v2 u3 v3)
      (cword a1 a2 a3 q u1 v1 u2 v2 u3 v3) = 1 := by
  let c := cword a1 a2 a3 q u1 v1 u2 v2 u3 v3
  have hs := cword_support a1 a2 a3 q u1 v1 u2 v2 u3 v3
  rw [SixQubit.innerC_self_eq_massOn S0 c hs, mass_bottom]
  dsimp [c]
  rw [cword_x0, cword_x1, cword_x2, cword_x3, cword_x4,
    cword_x5, cword_x6, cword_x7, cword_x8, cword_x9]
  simp only [Complex.normSq_neg, Complex.normSq_mul, normSq_phase,
    Complex.normSq_ofReal]
  have hu1 : u1^2 + (-v1)^2 = 1 := by nlinarith [hp.unit1]
  have hu2 : u2^2 + (-v2)^2 = 1 := by nlinarith [hp.unit2]
  have hu3 : u3^2 + (-v3)^2 = 1 := by nlinarith [hp.unit3]
  rw [hu1, hu2, hu3]
  norm_num
  have hr : 2*a1^2 + 2*a2^2 + 2*a3^2 + 4*q^2 = 1 := by
    nlinarith [hp.amp_sum, hp.q_sq]
  calc
    _ = (((2*a1^2 + 2*a2^2 + 2*a3^2 + 4*q^2 : ℝ)) : ℂ) := by
      push_cast
      ring
    _ = 1 := by rw [hr]; norm_num

theorem dword_normalized
    (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ)
    (hp : Params a1 a2 a3 q u1 v1 u2 v2 u3 v3) :
    SS.innerC (dword a1 a2 a3 q u1 v1 u2 v2 u3 v3)
      (dword a1 a2 a3 q u1 v1 u2 v2 u3 v3) = 1 := by
  let d := dword a1 a2 a3 q u1 v1 u2 v2 u3 v3
  have hs := dword_support a1 a2 a3 q u1 v1 u2 v2 u3 v3
  rw [SixQubit.innerC_self_eq_massOn S1 d hs, mass_top]
  dsimp [d]
  rw [dword_y0, dword_y1, dword_y2, dword_y3, dword_y4,
    dword_y5, dword_y6, dword_y7, dword_y8, dword_y9]
  simp only [Complex.normSq_neg, Complex.normSq_mul, normSq_phase,
    Complex.normSq_ofReal]
  rw [hp.unit1, hp.unit2, hp.unit3]
  norm_num
  have hr : 2*a1^2 + 2*a2^2 + 2*a3^2 + 4*q^2 = 1 := by
    nlinarith [hp.amp_sum, hp.q_sq]
  calc
    _ = (((2*a1^2 + 2*a2^2 + 2*a3^2 + 4*q^2 : ℝ)) : ℂ) := by
      push_cast
      ring
    _ = 1 := by rw [hr]; norm_num

private theorem normSq_phase_mul (u v a : ℝ) (hunit : u^2 + v^2 = 1) :
    Complex.normSq (phase u v * (a : ℂ)) = a^2 := by
  rw [Complex.normSq_mul, normSq_phase, Complex.normSq_ofReal, hunit]
  ring

/-- The direct amplitudes have exactly the five block masses used by the
universal converse. -/
theorem direct_block_masses
    (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ)
    (hp : Params a1 a2 a3 q u1 v1 u2 v2 u3 v3) :
    BlockMasses
      (cword a1 a2 a3 q u1 v1 u2 v2 u3 v3)
      (dword a1 a2 a3 q u1 v1 u2 v2 u3 v3)
      (4*a1^2) (4*a2^2) (4*a3^2) := by
  let c := cword a1 a2 a3 q u1 v1 u2 v2 u3 v3
  let d := dword a1 a2 a3 q u1 v1 u2 v2 u3 v3
  have hu1n : u1^2 + (-v1)^2 = 1 := by nlinarith [hp.unit1]
  have hu2n : u2^2 + (-v2)^2 = 1 := by nlinarith [hp.unit2]
  have hu3n : u3^2 + (-v3)^2 = 1 := by nlinarith [hp.unit3]
  refine ⟨by positivity, by positivity, by positivity,
    by nlinarith [hp.amp_sum], ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [c,d]
    rw [cword_x0, cword_x1, dword_y0, dword_y1]
    simp only [Complex.normSq_neg, Complex.normSq_ofReal]
    rw [normSq_phase_mul u1 (-v1) a1 hu1n,
      normSq_phase_mul u1 v1 a1 hp.unit1]
    norm_num
    ring
  · dsimp [c,d]
    rw [cword_x2, cword_x3, dword_y2, dword_y3]
    simp only [Complex.normSq_neg, Complex.normSq_ofReal]
    rw [normSq_phase_mul u2 (-v2) a2 hu2n,
      normSq_phase_mul u2 v2 a2 hp.unit2]
    norm_num
    ring
  · dsimp [c,d]
    rw [cword_x4, cword_x5, dword_y4, dword_y5]
    simp only [Complex.normSq_neg, Complex.normSq_ofReal]
    rw [normSq_phase_mul u3 (-v3) a3 hu3n,
      normSq_phase_mul u3 v3 a3 hp.unit3]
    norm_num
    ring
  · dsimp [c,d]
    rw [cword_x6, cword_x7, dword_y6, dword_y7]
    simp only [Complex.normSq_ofReal]
    have hq : q*q = 1/8 := by nlinarith [hp.q_sq]
    simp [hq]
  · dsimp [c,d]
    rw [cword_x8, cword_x9, dword_y8, dword_y9]
    simp only [Complex.normSq_neg, Complex.normSq_ofReal]
    have hq : q*q = 1/8 := by nlinarith [hp.q_sq]
    simp [hq]

/-- Converse bridge for the support rows.  This is the exact KL predicate,
not a moment-only surrogate. -/
theorem hasDistance_of_support_rows
    (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hdiag : ∀ e z, (⟨e,z⟩ : SS.PauliString 6).wt ≤ 2 →
      SixQubit.diagOn S0 c e z = SixQubit.diagOn S1 d e z)
    (hoff : ∀ e z, (⟨e,z⟩ : SS.PauliString 6).wt ≤ 2 →
      SixQubit.offSumOn S0 S1 c d e z = 0)
    (hrev : ∀ e z, (⟨e,z⟩ : SS.PauliString 6).wt ≤ 2 →
      SixQubit.offSumOn S1 S0 d c e z = 0) :
    SS.HasDistance ![c,d] 3 := by
  intro P hw
  refine ⟨Complex.I ^ P.numY * SixQubit.diagOn S0 c P.x P.z, ?_⟩
  intro j k
  fin_cases j <;> fin_cases k
  · change SS.innerC c (SS.pauliAct P c) = _
    rw [if_pos rfl,
      SixQubit.innerC_eq_diagOn S0 c hc]
  · change SS.innerC c (SS.pauliAct P d) = 0
    rw [SixQubit.innerC_eq_offSumOn S0 S1 c d hc hd, hoff P.x P.z hw,
      mul_zero]
  · change SS.innerC d (SS.pauliAct P c) = 0
    rw [SixQubit.innerC_eq_offSumOn S1 S0 d c hd hc, hrev P.x P.z hw,
      mul_zero]
  · change SS.innerC d (SS.pauliAct P d) = _
    rw [if_pos rfl,
      SixQubit.innerC_eq_diagOn S1 d hd, ← hdiag P.x P.z hw]

set_option linter.unusedSimpArgs false in
private theorem diag_zero_bit_one_sanity
    (a1 a2 a3 q u1 v1 u2 v2 u3 v3 : ℝ)
    (hp : Params a1 a2 a3 q u1 v1 u2 v2 u3 v3) :
    SixQubit.diagOn S0 (cword a1 a2 a3 q u1 v1 u2 v2 u3 v3)
        Orbit45A2.e00 (nbit 1) =
      SixQubit.diagOn S1 (dword a1 a2 a3 q u1 v1 u2 v2 u3 v3)
        Orbit45A2.e00 (nbit 1) := by
  unfold SixQubit.diagOn
  rw [show S0.filter (fun x => SS.bxor x Orbit45A2.e00 ∈ S0) =
      ({x0,x1,x2,x3,x4,x5,x6,x7,x8,x9} : Finset (SS.BitString 6)) from by decide,
    show S1.filter (fun x => SS.bxor x Orbit45A2.e00 ∈ S1) =
      ({y0,y1,y2,y3,y4,y5,y6,y7,y8,y9} : Finset (SS.BitString 6)) from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    show SS.bxor x0 Orbit45A2.e00 = x0 from by decide,
    show SS.bxor x1 Orbit45A2.e00 = x1 from by decide,
    show SS.bxor x2 Orbit45A2.e00 = x2 from by decide,
    show SS.bxor x3 Orbit45A2.e00 = x3 from by decide,
    show SS.bxor x4 Orbit45A2.e00 = x4 from by decide,
    show SS.bxor x5 Orbit45A2.e00 = x5 from by decide,
    show SS.bxor x6 Orbit45A2.e00 = x6 from by decide,
    show SS.bxor x7 Orbit45A2.e00 = x7 from by decide,
    show SS.bxor x8 Orbit45A2.e00 = x8 from by decide,
    show SS.bxor x9 Orbit45A2.e00 = x9 from by decide,
    show SS.bxor y0 Orbit45A2.e00 = y0 from by decide,
    show SS.bxor y1 Orbit45A2.e00 = y1 from by decide,
    show SS.bxor y2 Orbit45A2.e00 = y2 from by decide,
    show SS.bxor y3 Orbit45A2.e00 = y3 from by decide,
    show SS.bxor y4 Orbit45A2.e00 = y4 from by decide,
    show SS.bxor y5 Orbit45A2.e00 = y5 from by decide,
    show SS.bxor y6 Orbit45A2.e00 = y6 from by decide,
    show SS.bxor y7 Orbit45A2.e00 = y7 from by decide,
    show SS.bxor y8 Orbit45A2.e00 = y8 from by decide,
    show SS.bxor y9 Orbit45A2.e00 = y9 from by decide]
  simp only [show SS.bdot (nbit 1) x0 = false from by decide,
    show SS.bdot (nbit 1) x1 = true from by decide,
    show SS.bdot (nbit 1) x2 = false from by decide,
    show SS.bdot (nbit 1) x3 = true from by decide,
    show SS.bdot (nbit 1) x4 = false from by decide,
    show SS.bdot (nbit 1) x5 = true from by decide,
    show SS.bdot (nbit 1) x6 = false from by decide,
    show SS.bdot (nbit 1) x7 = true from by decide,
    show SS.bdot (nbit 1) x8 = false from by decide,
    show SS.bdot (nbit 1) x9 = true from by decide,
    show SS.bdot (nbit 1) y0 = false from by decide,
    show SS.bdot (nbit 1) y1 = true from by decide,
    show SS.bdot (nbit 1) y2 = false from by decide,
    show SS.bdot (nbit 1) y3 = true from by decide,
    show SS.bdot (nbit 1) y4 = false from by decide,
    show SS.bdot (nbit 1) y5 = true from by decide,
    show SS.bdot (nbit 1) y6 = false from by decide,
    show SS.bdot (nbit 1) y7 = true from by decide,
    show SS.bdot (nbit 1) y8 = false from by decide,
    show SS.bdot (nbit 1) y9 = true from by decide,
    SixQubit.signMul_false, SixQubit.signMul_true,
    cword_x0, cword_x1, cword_x2, cword_x3, cword_x4,
    cword_x5, cword_x6, cword_x7, cword_x8, cword_x9,
    dword_y0, dword_y1, dword_y2, dword_y3, dword_y4,
    dword_y5, dword_y6, dword_y7, dword_y8, dword_y9]
  simp only [star_neg, star_mul', star_phase, Complex.star_def,
    Complex.conj_ofReal]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      phase_re, phase_im, Complex.ofReal_re, Complex.ofReal_im]
  · nlinarith [hp.unit1, hp.unit2, hp.unit3]
  · ring

end

end SixQubit.Orbit45Attain
