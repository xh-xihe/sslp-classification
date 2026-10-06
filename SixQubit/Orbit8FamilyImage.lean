import SixQubit.Orbit8FamilyEnum
import SixQubit.Pin

/-!
# Orbit 8 family: the full enumerator image and interval attainment

This layer packages the sparse low-weight trace certificate, derives the
weight-three zero from the kernel-proved shadow inequality, and then obtains
all remaining `A` and `B` coefficients from the two exact MacWilliams
transforms.
-/

namespace SixQubit.Orbit8Family

open scoped BigOperators
open SS.MacWilliams

set_option maxRecDepth 20000

noncomputable section

def alpha (C S : ℝ) : ℝ := C^4 + S^4

def IsFamilyA (psi : Fin 2 → SS.State 6 ℂ) (a : ℝ) : Prop :=
  Aco psi 0 = 4 ∧ Aco psi 1 = 4*a ∧ Aco psi 2 = 4*(1-a) ∧
    Aco psi 3 = 0 ∧ Aco psi 4 = 4*(11+4*a) ∧
    Aco psi 5 = 4*(16-a) ∧ Aco psi 6 = 4*(3-3*a)

def IsFamilyB (psi : Fin 2 → SS.State 6 ℂ) (a : ℝ) : Prop :=
  Bco psi 0 = 4 ∧ Bco psi 1 = 4*a ∧ Bco psi 2 = 4*(1-a) ∧
    Bco psi 3 = 4*(24+6*a) ∧ Bco psi 4 = 4*(35+10*a) ∧
    Bco psi 5 = 4*(40-7*a) ∧ Bco psi 6 = 4*(27-9*a)

lemma wt_PId : PId.wt = 0 := by decide
lemma wt_PZ0 : PZ0.wt = 1 := by decide
lemma wt_PZ4 : PZ4.wt = 1 := by decide
lemma wt_PXX : PXX.wt = 2 := by decide
lemma wt_PYY : PYY.wt = 2 := by decide

theorem normalized (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    ∀ k, SS.innerC (code C S k) (code C S k) = 1 := by
  intro k
  fin_cases k
  · exact w0_normalized C S hCS
  · exact w1_normalized C S hCS

theorem Aco_zero_family (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (code C S) 0 = 4 := SixQubit.Pin.Aco_zero _ (normalized C S hCS)

lemma normSq_trace_low (C S : ℝ) (hCS : C^2 + S^2 = 1)
    (P : SS.PauliString 6) (hwt : P.wt ≤ 2) (hi : P ≠ PId) :
    Complex.normSq (trProj (code C S) P) =
      if P = PZ0 then 4*S^4 else if P = PZ4 then 4*C^4
      else if P = PXX then 4*C^2*S^2 else if P = PYY then 4*C^2*S^2 else 0 := by
  by_cases h0 : P = PZ0
  · subst P
    simp only [if_pos, trProj_Z0 C S hCS, Complex.normSq_ofReal]
    ring
  rw [if_neg h0]
  by_cases h4 : P = PZ4
  · subst P
    simp only [if_pos, trProj_Z4 C S hCS, Complex.normSq_ofReal]
    ring
  rw [if_neg h4]
  by_cases hx : P = PXX
  · subst P
    simp only [if_pos, trProj_XX, Complex.normSq_ofReal]
    ring
  rw [if_neg hx]
  by_cases hy : P = PYY
  · subst P
    simp only [if_pos, trProj_YY, Complex.normSq_ofReal]
    ring
  rw [if_neg hy, trProj_sparse C S hCS P hwt hi h0 h4 hx hy, Complex.normSq_zero]

lemma normSq_Z0 (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Complex.normSq (trProj (code C S) PZ0) = 4*S^4 := by
  rw [trProj_Z0 C S hCS, Complex.normSq_ofReal]
  ring

lemma normSq_Z4 (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Complex.normSq (trProj (code C S) PZ4) = 4*C^4 := by
  rw [trProj_Z4 C S hCS, Complex.normSq_ofReal]
  ring

lemma normSq_XX (C S : ℝ) :
    Complex.normSq (trProj (code C S) PXX) = 4*C^2*S^2 := by
  rw [trProj_XX, Complex.normSq_ofReal]
  ring

lemma normSq_YY (C S : ℝ) :
    Complex.normSq (trProj (code C S) PYY) = 4*C^2*S^2 := by
  rw [trProj_YY, Complex.normSq_ofReal]
  ring

theorem Aco_one (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (code C S) 1 = 4 * alpha C S := by
  classical
  let U := Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 1)
  let T : Finset (SS.PauliString 6) := {PZ0, PZ4}
  have hterm : ∀ P ∈ Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 1),
      Complex.normSq (trProj (code C S) P) =
        if P = PZ0 then 4*S^4 else if P = PZ4 then 4*C^4
        else if P = PXX then 4*C^2*S^2 else if P = PYY then 4*C^2*S^2 else 0 := by
    intro P hP
    have hw : P.wt = 1 := (Finset.mem_filter.mp hP).2
    apply normSq_trace_low C S hCS P (by omega)
    intro hi
    rw [hi] at hw
    rw [wt_PId] at hw
    omega
  have hsub : T ⊆ U := by
    intro P hP
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · simpa [U] using wt_PZ0
    · simpa [U] using wt_PZ4
  have hout : ∀ P ∈ U, P ∉ T →
      Complex.normSq (trProj (code C S) P) = 0 := by
    intro P hP hPT
    have hm : P ≠ PZ0 ∧ P ≠ PZ4 := by simpa [T] using hPT
    have ht := hterm P (by simpa [U] using hP)
    have hw : P.wt = 1 := by simpa [U] using hP
    have hx : P ≠ PXX := by intro h; rw [h, wt_PXX] at hw; omega
    have hy : P ≠ PYY := by intro h; rw [h, wt_PYY] at hw; omega
    simpa [hm.1, hm.2, hx, hy] using ht
  have hsum := Finset.sum_subset hsub hout
  change (∑ P ∈ T, Complex.normSq (trProj (code C S) P)) =
    (∑ P ∈ U, Complex.normSq (trProj (code C S) P)) at hsum
  rw [Aco]
  change (∑ P ∈ U, Complex.normSq (trProj (code C S) P)) = _
  rw [← hsum]
  dsimp [T]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton,
    normSq_Z0 C S hCS, normSq_Z4 C S hCS]
  unfold alpha
  ring

theorem Aco_two (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    Aco (code C S) 2 = 8 * C^2 * S^2 := by
  classical
  let U := Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 2)
  let T : Finset (SS.PauliString 6) := {PXX, PYY}
  have hterm : ∀ P ∈ Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 2),
      Complex.normSq (trProj (code C S) P) =
        if P = PZ0 then 4*S^4 else if P = PZ4 then 4*C^4
        else if P = PXX then 4*C^2*S^2 else if P = PYY then 4*C^2*S^2 else 0 := by
    intro P hP
    have hw : P.wt = 2 := (Finset.mem_filter.mp hP).2
    apply normSq_trace_low C S hCS P (by omega)
    intro hi
    rw [hi] at hw
    rw [wt_PId] at hw
    omega
  have hsub : T ⊆ U := by
    intro P hP
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · simpa [U] using wt_PXX
    · simpa [U] using wt_PYY
  have hout : ∀ P ∈ U, P ∉ T →
      Complex.normSq (trProj (code C S) P) = 0 := by
    intro P hP hPT
    have hm : P ≠ PXX ∧ P ≠ PYY := by simpa [T] using hPT
    have ht := hterm P (by simpa [U] using hP)
    have hw : P.wt = 2 := by simpa [U] using hP
    have h0 : P ≠ PZ0 := by intro h; rw [h, wt_PZ0] at hw; omega
    have h4 : P ≠ PZ4 := by intro h; rw [h, wt_PZ4] at hw; omega
    simpa [h0, h4, hm.1, hm.2] using ht
  have hsum := Finset.sum_subset hsub hout
  change (∑ P ∈ T, Complex.normSq (trProj (code C S) P)) =
    (∑ P ∈ U, Complex.normSq (trProj (code C S) P)) at hsum
  rw [Aco]
  change (∑ P ∈ U, Complex.normSq (trProj (code C S) P)) = _
  rw [← hsum]
  dsimp [T]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, normSq_XX, normSq_YY]
  ring

lemma alpha_complement (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    2*C^2*S^2 = 1 - alpha C S := by
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

/-- The complete `A` enumerator of every member of the explicit circle
family. -/
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

/-- The complete `B` enumerator, derived from the exact six-qubit quantum
MacWilliams transform. -/
theorem family_B (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    IsFamilyB (code C S) (alpha C S) := by
  rcases family_A C S hCS with ⟨h0,h1,h2,h3,h4,h5,h6⟩
  rcases bco_transform_six (code C S) with ⟨b0,b1,b2,b3,b4,b5,b6⟩
  dsimp only [IsFamilyB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem alpha_bounds (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    (1/2 : ℝ) ≤ alpha C S ∧ alpha C S ≤ 1 := by
  unfold alpha
  constructor
  · nlinarith [sq_nonneg (C^2 - S^2)]
  · nlinarith [sq_nonneg (C*S)]

/-- Every point of `[1/2,1]` has real circle parameters with precisely that
value of `C^4+S^4`. -/
theorem circle_parameters (a : ℝ) (ha0 : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∃ C S : ℝ, C^2 + S^2 = 1 ∧ alpha C S = a := by
  let d : ℝ := Real.sqrt (2*a - 1)
  have hrad : 0 ≤ 2*a - 1 := by linarith
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  have hd2 : d^2 = 2*a - 1 := by
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

/-- **Exact interval attainment for orbit 8.**  For every manuscript parameter
`a in [1/2,1]`, this produces a genuine distance-three pair, supported in the
two complete orbit-8 fibers, with exactly the displayed `A` and `B`
enumerators. -/
theorem attain (a : ℝ) (ha0 : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∃ C S : ℝ, C^2 + S^2 = 1 ∧ alpha C S = a ∧
      SS.HasDistance (code C S) 3 ∧
      (∀ x, SS.weight SixQubit.Orbit8Real.av x ≠ 0 → w0 C S x = 0) ∧
      (∀ x, SS.weight SixQubit.Orbit8Real.av x ≠ 1 → w1 C S x = 0) ∧
      IsFamilyA (code C S) a ∧ IsFamilyB (code C S) a := by
  obtain ⟨C,S,hCS,ha⟩ := circle_parameters a ha0 ha1
  refine ⟨C,S,hCS,ha,is_code C S hCS,w0_full_fiber C S,w1_full_fiber C S,?_,?_⟩
  · simpa [ha] using family_A C S hCS
  · simpa [ha] using family_B C S hCS

end

end SixQubit.Orbit8Family
