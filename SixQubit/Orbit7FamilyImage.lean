import SixQubit.Orbit7FamilyEnum
import SixQubit.Pin

/-!
# Orbit 7 circle family: complete enumerators and interval attainment

The exact sparse traces from `Orbit7FamilyEnum` imply

```
  A_1 = 4 a,       A_2 = 4 (1-a),       a = 4 C^2 S^2.
```

The six-qubit shadow inequality forces `A_3=0`; the remaining `A` and all
`B` coefficients follow from the kernel-proved MacWilliams identities.  The
last theorem constructs real circle parameters for every `a in [0,1]`, so
this is pointwise interval attainment, not merely endpoint realization.
-/

namespace SixQubit.Orbit7Family

open scoped BigOperators
open SS.MacWilliams

set_option maxRecDepth 20000

noncomputable section

def alpha (C S : ℝ) : ℝ := 4*C^2*S^2

def IsFamilyA (psi : Fin 2 -> SS.State 6 ℂ) (a : ℝ) : Prop :=
  Aco psi 0 = 4 ∧ Aco psi 1 = 4*a ∧ Aco psi 2 = 4*(1-a) ∧
    Aco psi 3 = 0 ∧ Aco psi 4 = 4*(11+4*a) ∧
    Aco psi 5 = 4*(16-a) ∧ Aco psi 6 = 4*(3-3*a)

def IsFamilyB (psi : Fin 2 -> SS.State 6 ℂ) (a : ℝ) : Prop :=
  Bco psi 0 = 4 ∧ Bco psi 1 = 4*a ∧ Bco psi 2 = 4*(1-a) ∧
    Bco psi 3 = 4*(24+6*a) ∧ Bco psi 4 = 4*(35+10*a) ∧
    Bco psi 5 = 4*(40-7*a) ∧ Bco psi 6 = 4*(27-9*a)

lemma wt_PId : PId.wt = 0 := by decide
lemma wt_PX0 : PX0.wt = 1 := by decide
lemma wt_PZ02 : PZ02.wt = 2 := by decide

theorem Aco_zero_family (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (code C S) 0 = 4 :=
  SixQubit.Pin.Aco_zero _ (normalized C S hCS)

lemma normSq_trace_low (C S : ℝ) (hCS : C^2 + S^2 = 1)
    (P : SS.PauliString 6) (hwt : P.wt ≤ 2) (hi : P ≠ PId) :
    Complex.normSq (trProj (code C S) P) =
      if P = PX0 then 16*C^2*S^2
      else if P = PZ02 then 4*(C^2-S^2)^2
      else 0 := by
  by_cases hx : P = PX0
  · subst P
    simp only [if_pos, trProj_X0, Complex.normSq_ofReal]
    ring
  rw [if_neg hx]
  by_cases hz : P = PZ02
  · subst P
    simp only [if_pos, trProj_Z02, Complex.normSq_ofReal]
    ring
  rw [if_neg hz, trProj_sparse C S hCS P hwt hi hx hz, Complex.normSq_zero]

lemma normSq_X0 (C S : ℝ) :
    Complex.normSq (trProj (code C S) PX0) = 16*C^2*S^2 := by
  rw [trProj_X0, Complex.normSq_ofReal]
  ring

lemma normSq_Z02 (C S : ℝ) :
    Complex.normSq (trProj (code C S) PZ02) = 4*(C^2-S^2)^2 := by
  rw [trProj_Z02, Complex.normSq_ofReal]
  ring

theorem Aco_one (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (code C S) 1 = 4 * alpha C S := by
  classical
  let U := Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 1)
  let T : Finset (SS.PauliString 6) := {PX0}
  have hsub : T ⊆ U := by
    intro P hP
    simp only [T, Finset.mem_singleton] at hP
    subst P
    simpa [U] using wt_PX0
  have hout : ∀ P ∈ U, P ∉ T ->
      Complex.normSq (trProj (code C S) P) = 0 := by
    intro P hP hPT
    have hx : P ≠ PX0 := by simpa [T] using hPT
    have hw : P.wt = 1 := by simpa [U] using hP
    have hi : P ≠ PId := by intro h; rw [h, wt_PId] at hw; omega
    have hz : P ≠ PZ02 := by intro h; rw [h, wt_PZ02] at hw; omega
    simpa [hx, hz] using normSq_trace_low C S hCS P (by omega) hi
  have hsum := Finset.sum_subset hsub hout
  change (∑ P ∈ T, Complex.normSq (trProj (code C S) P)) =
    (∑ P ∈ U, Complex.normSq (trProj (code C S) P)) at hsum
  rw [Aco]
  change (∑ P ∈ U, Complex.normSq (trProj (code C S) P)) = _
  rw [← hsum]
  dsimp [T]
  rw [Finset.sum_singleton, normSq_X0]
  unfold alpha
  ring

theorem Aco_two (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (code C S) 2 = 4 * (C^2-S^2)^2 := by
  classical
  let U := Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 2)
  let T : Finset (SS.PauliString 6) := {PZ02}
  have hsub : T ⊆ U := by
    intro P hP
    simp only [T, Finset.mem_singleton] at hP
    subst P
    simpa [U] using wt_PZ02
  have hout : ∀ P ∈ U, P ∉ T ->
      Complex.normSq (trProj (code C S) P) = 0 := by
    intro P hP hPT
    have hz : P ≠ PZ02 := by simpa [T] using hPT
    have hw : P.wt = 2 := by simpa [U] using hP
    have hi : P ≠ PId := by intro h; rw [h, wt_PId] at hw; omega
    have hx : P ≠ PX0 := by intro h; rw [h, wt_PX0] at hw; omega
    simpa [hx, hz] using normSq_trace_low C S hCS P (by omega) hi
  have hsum := Finset.sum_subset hsub hout
  change (∑ P ∈ T, Complex.normSq (trProj (code C S) P)) =
    (∑ P ∈ U, Complex.normSq (trProj (code C S) P)) at hsum
  rw [Aco]
  change (∑ P ∈ U, Complex.normSq (trProj (code C S) P)) = _
  rw [← hsum]
  dsimp [T]
  rw [Finset.sum_singleton, normSq_Z02]

lemma alpha_complement (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    (C^2-S^2)^2 = 1 - alpha C S := by
  unfold alpha
  nlinarith [sq_nonneg (C^2 + S^2)]

theorem Aco_three (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (code C S) 3 = 0 := by
  have h0 := Aco_zero_family C S hCS
  have hsh := SS.Shadow.shadow_bound (code C S) (is_code C S hCS) h0
  have h3 := SixQubit.Pin.Aco_nonneg (code C S) 3
  rw [Aco_one C S hCS, Aco_two C S hCS] at hsh
  have ha := alpha_complement C S hCS
  nlinarith

theorem family_A (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    IsFamilyA (code C S) (alpha C S) := by
  have h0 := Aco_zero_family C S hCS
  have h1 := Aco_one C S hCS
  have h2raw := Aco_two C S hCS
  have ha := alpha_complement C S hCS
  have h2 : Aco (code C S) 2 = 4*(1-alpha C S) := by nlinarith
  have h3 := Aco_three C S hCS
  obtain ⟨h4, h5, h6⟩ := macwilliams_six (code C S) (is_code C S hCS) h0
  dsimp only [IsFamilyA]
  refine ⟨h0, h1, h2, h3, ?_, ?_, ?_⟩ <;> linarith

theorem family_B (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    IsFamilyB (code C S) (alpha C S) := by
  rcases family_A C S hCS with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  rcases bco_transform_six (code C S) with ⟨b0,b1,b2,b3,b4,b5,b6⟩
  dsimp only [IsFamilyB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem alpha_bounds (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    (0 : ℝ) ≤ alpha C S ∧ alpha C S ≤ 1 := by
  have hc : 0 ≤ C^2 := sq_nonneg C
  have hs : 0 ≤ S^2 := sq_nonneg S
  have hcomp := alpha_complement C S hCS
  constructor
  · unfold alpha
    positivity
  · nlinarith [sq_nonneg (C^2-S^2)]

/-- Exact real circle parameters for every `a in [0,1]`. -/
theorem circle_parameters (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ C S : ℝ, C^2 + S^2 = 1 ∧ alpha C S = a := by
  let d : ℝ := Real.sqrt (1-a)
  have hrad : 0 ≤ 1-a := by linarith
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2 = 1-a := by
    dsimp [d]
    exact Real.sq_sqrt hrad
  have hd1 : d ≤ 1 := by nlinarith
  let t : ℝ := (1+d)/2
  let u : ℝ := (1-d)/2
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 ≤ u := by dsimp [u]; linarith
  let C := Real.sqrt t
  let S := Real.sqrt u
  have hC : C^2 = t := by dsimp [C]; exact Real.sq_sqrt ht
  have hS : S^2 = u := by dsimp [S]; exact Real.sq_sqrt hu
  refine ⟨C, S, ?_, ?_⟩
  · dsimp [t, u] at hC hS ⊢
    nlinarith
  · unfold alpha
    dsimp [t, u] at hC hS ⊢
    nlinarith

/-- **Pointwise exact interval attainment for orbit 7.** -/
theorem attain (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ C S : ℝ, C^2 + S^2 = 1 ∧ alpha C S = a ∧
      SS.HasDistance (code C S) 3 ∧
      (∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 0 -> w0 C S x = 0) ∧
      (∀ x, SS.weight SixQubit.Orbit7Real.av x ≠ 1 -> w1 C S x = 0) ∧
      IsFamilyA (code C S) a ∧ IsFamilyB (code C S) a := by
  obtain ⟨C,S,hCS,ha⟩ := circle_parameters a ha0 ha1
  refine ⟨C,S,hCS,ha,is_code C S hCS,w0_full_fiber C S,w1_full_fiber C S,?_,?_⟩
  · simpa [ha] using family_A C S hCS
  · simpa [ha] using family_B C S hCS

end

end SixQubit.Orbit7Family
