import MainTheory.CodeSpec
import MainTheory.RealGate
import MainTheory.Gate
import MainTheory.SSLPConverse
import MainTheory.GeneralLiftOrder

/-!
# The five-qubit finite-lift example

The explicit supports and physical one-parameter family of
`main.tex`, `ex:five-qubit-rationalization`. Finite Pauli correlations are
computed over the integers and transported to the actual complex states.
-/

namespace MainTheory.FiveQubitRationalization

open scoped BigOperators

def bs (a b c d e : Bool) : SS.BitString 5 := ![a, b, c, d, e]

def support0 : Finset (SS.BitString 5) :=
  {bs false false false false false,
   bs true false false false true,
   bs true true true true false}

def support1 : Finset (SS.BitString 5) :=
  {bs false false false true true,
   bs true false true false false,
   bs true true false false false}

def raw (i : Fin 2) (x : SS.BitString 5) : ℤ :=
  if x ∈ (if i = 0 then support0 else support1) then 1 else 0

def point (i : Fin 2) : Fin 3 → SS.BitString 5 :=
  if i = 0 then ![bs false false false false false,
    bs true false false false true, bs true true true true false]
  else ![bs false false false true true,
    bs true false true false false, bs true true false false false]

def correlation (i j : Fin 2) (P : SS.PauliString 5) : ℤ :=
  ∑ k : Fin 3, (if SS.bdot P.z (point j k) then -1 else 1) *
    raw i (SS.bxor (point j k) P.x)

theorem sum_mul_raw {R : Type*} [Ring R] (j : Fin 2) (f : SS.BitString 5 → R) :
    (∑ x, f x * (raw j x : R)) = ∑ k : Fin 3, f (point j k) := by
  classical
  calc
    _ = ∑ x, if x ∈ (if j = 0 then support0 else support1) then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : x ∈ (if j = 0 then support0 else support1) <;> simp [raw, h]
    _ = ∑ x ∈ (if j = 0 then support0 else support1), f x := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    _ = _ := by
      fin_cases j <;> simp [point, support0, support1, Fin.sum_univ_succ, bs]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem raw_gram : ∀ i j : Fin 2,
    (∑ k : Fin 3, raw i (point j k)) = if i = j then 3 else 0 := by
  decide

def num (x : SS.BitString 5) : ℕ :=
  (if x 0 then 1 else 0) + (if x 1 then 2 else 0) + (if x 2 then 4 else 0) +
    (if x 3 then 8 else 0) + (if x 4 then 16 else 0)

def nbit (m : ℕ) : SS.BitString 5 := fun i => Nat.testBit m i.val

theorem nbit_num : ∀ x, nbit (num x) = x := by decide
theorem num_lt : ∀ x, num x < 32 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem low_weight_correlations_mask : ∀ x < 32, ∀ z < 32,
    (⟨nbit x, nbit z⟩ : SS.PauliString 5).wt ≤ 1 →
    correlation 0 1 ⟨nbit x, nbit z⟩ = 0 ∧
    correlation 1 0 ⟨nbit x, nbit z⟩ = 0 ∧
    correlation 0 0 ⟨nbit x, nbit z⟩ = correlation 1 1 ⟨nbit x, nbit z⟩ := by
  decide

theorem low_weight_correlations (P : SS.PauliString 5) (hP : P.wt ≤ 1) :
    correlation 0 1 P = 0 ∧ correlation 1 0 P = 0 ∧
      correlation 0 0 P = correlation 1 1 P := by
  have h := low_weight_correlations_mask (num P.x) (num_lt P.x)
    (num P.z) (num_lt P.z)
  simp only [nbit_num] at h
  exact h hP

noncomputable def amplitude : ℂ := (Real.sqrt 3 : ℂ) / 3

noncomputable def state (i : Fin 2) : SS.State 5 ℂ :=
  fun x => amplitude * (raw i x : ℂ)

theorem amplitude_square : star amplitude * amplitude = (1 / 3 : ℂ) := by
  have hs : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : (Real.sqrt (3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast hs
  simp only [amplitude, star_div₀, Complex.star_def, map_ofNat,
    Complex.conj_ofReal]
  linear_combination (1 / 9 : ℂ) * hc

theorem inner_state (i j : Fin 2) :
    SS.innerC (state i) (state j) = if i = j then 1 else 0 := by
  classical
  calc
    SS.innerC (state i) (state j) =
        (star amplitude * amplitude) * ∑ x, (raw i x : ℂ) * (raw j x : ℂ) := by
      rw [SS.innerC, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [state, star_mul, star_intCast]
      ring
    _ = (1 / 3 : ℂ) * ((∑ k : Fin 3, raw i (point j k) : ℤ) : ℂ) := by
      rw [amplitude_square, sum_mul_raw]
      push_cast
      rfl
    _ = if i = j then 1 else 0 := by
      rw [raw_gram]
      split_ifs <;> norm_num

theorem pauli_element (i j : Fin 2) (P : SS.PauliString 5) :
    SS.innerC (state i) (SS.pauliAct P (state j)) =
      (Complex.I ^ P.numY) * (1 / 3 : ℂ) * (correlation i j P : ℂ) := by
  classical
  rw [SS.innerC_pauliAct]
  have hcast : (correlation i j P : ℂ) = ∑ x,
      ((if SS.bdot P.z x then (-1 : ℂ) else 1) *
        (raw i (SS.bxor x P.x) : ℂ)) * (raw j x : ℂ) := by
    rw [sum_mul_raw]
    simp only [correlation, Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl
    intro k _
    cases SS.bdot P.z (point j k) <;> simp
  calc
    _ = (Complex.I ^ P.numY) *
        ((star amplitude * amplitude) * (correlation i j P : ℂ)) := by
      congr 1
      rw [hcast, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      cases SS.bdot P.z x <;>
        simp only [state, SS.signC, Bool.false_eq_true, if_false, if_true,
          star_mul, star_intCast] <;> ring
    _ = _ := by rw [amplitude_square]; ring

theorem hasDistance_two : SS.HasDistance state 2 := by
  intro P hP
  obtain ⟨h01, h10, hdiag⟩ := low_weight_correlations P hP
  refine ⟨(Complex.I ^ P.numY) * (1 / 3 : ℂ) * (correlation 0 0 P : ℂ), ?_⟩
  intro i j
  rw [pauli_element]
  fin_cases i <;> fin_cases j <;> simp [h01, h10, ← hdiag]

noncomputable def frame : CodeSpec.OrthonormalFrame 5 2 where
  vec := state
  orthonormal := inner_state

noncomputable def code : CodeSpec.ExactCode 5 2 2 where
  positiveRank := by norm_num
  frame := frame
  hasDistance := hasDistance_two

def zz23 : SS.PauliString 5 :=
  ⟨fun _ => false, bs false true true false false⟩

theorem zz23_data : zz23.wt = 2 ∧ zz23.numY = 0 ∧
    correlation 0 0 zz23 = 3 ∧ correlation 1 1 zz23 = -1 := by decide

theorem zz23_expectations :
    SS.innerC (state 0) (SS.pauliAct zz23 (state 0)) = 1 ∧
    SS.innerC (state 1) (SS.pauliAct zz23 (state 1)) = -(1 / 3 : ℂ) := by
  obtain ⟨_, hy, h0, h1⟩ := zz23_data
  simp only [pauli_element, hy, h0, h1]
  norm_num

theorem not_hasDistance_three : ¬ SS.HasDistance state 3 := by
  intro h
  obtain ⟨c, hc⟩ := h zz23 (by rw [zz23_data.1])
  have h0 := hc 0 0
  have h1 := hc 1 1
  rw [zz23_expectations.1] at h0
  rw [zz23_expectations.2] at h1
  have hc0 : c = 1 := by simpa using h0.symm
  norm_num [hc0] at h1

theorem normSq_amplitude : Complex.normSq amplitude = (1 / 3 : ℝ) := by
  apply Complex.ofReal_injective
  rw [Complex.normSq_eq_conj_mul_self]
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    using amplitude_square

theorem normSq_state (i : Fin 2) (x : SS.BitString 5) :
    Complex.normSq (state i x) = (1 / 3 : ℝ) * (raw i x : ℝ) := by
  rw [state, map_mul, normSq_amplitude]
  by_cases h : x ∈ (if i = 0 then support0 else support1) <;> simp [raw, h]

def commonMean : Fin 5 → ℚ := ![2/3, 1/3, 1/3, 1/3, 1/3]

theorem mean_count : ∀ i : Fin 2, ∀ j : Fin 5,
    (∑ k : Fin 3, if point i k j then (1 : ℤ) else 0) =
      if j = 0 then 2 else 1 := by decide

theorem first_moments (i : Fin 2) (j : Fin 5) :
    (∑ x, Complex.normSq (state i x) * (if x j then (1 : ℝ) else 0)) =
      (commonMean j : ℝ) := by
  simp only [normSq_state]
  have hs : (∑ x, (1 / 3 : ℝ) * (raw i x : ℝ) * (if x j then 1 else 0)) =
      (1 / 3 : ℝ) * ∑ x, (if x j then 1 else 0) * (raw i x : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hs, sum_mul_raw]
  have hcast : (∑ k : Fin 3, if point i k j then (1 : ℝ) else 0) =
      (((∑ k : Fin 3, if point i k j then (1 : ℤ) else 0) : ℤ) : ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    cases point i k j <;> simp
  rw [hcast]
  rw [mean_count i j]
  fin_cases j <;> norm_num [commonMean]

noncomputable def theta (t : ℝ) : Fin 5 → ℝ := ![t, 1/3-t, 1/3-t, 1/3+t, -t]

noncomputable def phase (t : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

theorem point_angles (t : ℝ) : ∀ k : Fin 3,
    RealGate.angle (theta t) (point 0 k) = (if k = 2 then 1 else 0) ∧
    RealGate.angle (theta t) (point 1 k) = 1/3 := by
  intro k
  fin_cases k <;>
    norm_num [RealGate.angle, theta, point, bs, Fin.sum_univ_succ, Fin.ext_iff]
  all_goals ring

theorem raw_supported : ∀ i x, raw i x ≠ 0 ↔
    x = point i 0 ∨ x = point i 1 ∨ x = point i 2 := by decide

theorem phase_zero : phase 0 = 1 := by simp [phase]

theorem phase_one : phase 1 = 1 := by
  simp [phase]

theorem phase_third_primitive : IsPrimitiveRoot (phase (1/3)) 3 := by
  unfold phase
  convert Complex.isPrimitiveRoot_exp 3 (by norm_num) using 1
  congr 1
  push_cast
  ring

theorem eigen_family (t : ℝ) (i : Fin 2) :
    RealGate.realGate (theta t) (state i) =
      fun x => (if i = 0 then 1 else phase (1/3)) * state i x := by
  funext x
  by_cases hx : raw i x = 0
  · simp [RealGate.realGate, state, hx]
  · obtain h | h | h := (raw_supported i x).mp hx <;> subst x <;>
      fin_cases i <;>
      change phase (RealGate.angle (theta t) _) * _ = _ <;>
      simp [point_angles, phase_zero, phase_one]

def angle6 : Fin 5 → ZMod 6 := ![1, 1, 1, 3, 5]
def angle3 : Fin 5 → ZMod 3 := ![0, 1, 1, 1, 0]

theorem angle6_primitive : Gate.Primitive 6 angle6 := by
  intro k _ hk
  have hv : (angle6 0).val = 1 := by decide
  have h := hk 0
  rw [hv] at h
  exact Nat.eq_one_of_dvd_one h

theorem angle3_primitive : Gate.Primitive 3 angle3 := by
  intro k _ hk
  have hv : (angle3 1).val = 1 := by decide
  have h := hk 1
  rw [hv] at h
  exact Nat.eq_one_of_dvd_one h

theorem point_fibres6 : ∀ k : Fin 3,
    SS.weight angle6 (point 0 k) = 0 ∧ SS.weight angle6 (point 1 k) = 2 := by
  decide

theorem point_fibres3 : ∀ k : Fin 3,
    SS.weight angle3 (point 0 k) = 0 ∧ SS.weight angle3 (point 1 k) = 1 := by
  decide

theorem state_fibres6 :
    SS.SSConditionState angle6 0 (state 0) ∧
    SS.SSConditionState angle6 2 (state 1) := by
  have hs (i : Fin 2) (x : SS.BitString 5) (hx : state i x ≠ 0) : raw i x ≠ 0 := by
      intro h
      exact hx (by simp [state, h])
  constructor <;> intro x hx
  all_goals
    obtain h | h | h := (raw_supported _ x).mp (hs _ x hx) <;> subst x
    all_goals simp [point_fibres6]

theorem state_fibres3 :
    SS.SSConditionState angle3 0 (state 0) ∧
    SS.SSConditionState angle3 1 (state 1) := by
  have hs (i : Fin 2) (x : SS.BitString 5) (hx : state i x ≠ 0) : raw i x ≠ 0 := by
      intro h
      exact hx (by simp [state, h])
  constructor <;> intro x hx
  all_goals
    obtain h | h | h := (raw_supported _ x).mp (hs _ x hx) <;> subst x
    all_goals simp [point_fibres3]

theorem phase_pow_eq_one_iff (t : ℝ) (k : ℕ) :
    phase t ^ k = 1 ↔ ∃ z : ℤ, (k : ℝ) * t = z := by
  rw [phase, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  have hc : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have he : (2 : ℂ) * Real.pi * Complex.I * ((k : ℂ) * t) =
        (2 : ℂ) * Real.pi * Complex.I * z := by
      calc
        _ = (k : ℂ) * (2 * Real.pi * Complex.I * t) := by ring
        _ = _ := hz.trans (by ring)
    exact_mod_cast mul_left_cancel₀ hc he
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have he : (k : ℂ) * t = z := by exact_mod_cast hz
    calc
      _ = (2 : ℂ) * Real.pi * Complex.I * ((k : ℂ) * t) := by ring
      _ = _ := by rw [he]; ring

theorem irrational_phase_infinite {t : ℝ} (ht : Irrational t)
    {k : ℕ} (hk : 0 < k) : phase t ^ k ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := (phase_pow_eq_one_iff t k).mp h
  exact (ht.natCast_mul hk.ne').ne_int z hz

theorem realGate_iterate (t : ℝ) (k : ℕ) (f : SS.State 5 ℂ) (x : SS.BitString 5) :
    ((RealGate.realGate (theta t))^[k] f) x =
      phase (RealGate.angle (theta t) x) ^ k * f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', RealGate.realGate, ih, pow_succ]
    change phase _ * (phase _ ^ k * _) = _
    ring

/-- The actual physical operator has no positive identity power. -/
theorem physical_infinite_order {t : ℝ} (ht : Irrational t)
    {k : ℕ} (hk : 0 < k) :
    (RealGate.realGate (theta t))^[k] ≠ id := by
  intro h
  have he := congrFun (congrFun h (fun _ => 1)) (bs true false false false false)
  rw [realGate_iterate] at he
  have ha : RealGate.angle (theta t) (bs true false false false false) = t := by
    simp [RealGate.angle, theta, bs, Fin.sum_univ_succ]
  rw [ha] at he
  exact irrational_phase_infinite ht hk (by simpa using he)

def AuxiliarySystem (v : Fin 5 → ℝ) (s : ℝ) : Prop :=
  v 0 + v 4 = 0 ∧ v 0 + v 1 + v 2 + v 3 = 1 ∧
  v 3 + v 4 - s = 0 ∧ v 0 + v 2 - s = 0 ∧ v 0 + v 1 - s = 0

theorem auxiliary_solutions (v : Fin 5 → ℝ) (s : ℝ) :
    AuxiliarySystem v s ↔ s = 1/3 ∧ v = theta (v 0) := by
  constructor
  · rintro ⟨h0, h1, h2, h3, h4⟩
    have hs : s = 1/3 := by linarith
    refine ⟨hs, ?_⟩
    ext j
    fin_cases j <;> simp [theta] <;> linarith
  · rintro ⟨rfl, hv⟩
    obtain ⟨t, rfl⟩ : ∃ t, v = theta t := ⟨v 0, hv⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [theta]
    all_goals ring

noncomputable def resolution3 : RankTwoGlobal.FiniteGeneratorResolution code 3 :=
  SSLPConverse.resolutionOfPair
    (D3NormalizedFiniteToReal.canonicalRoot_primitive 3) angle3_primitive
    (m := 3) (by norm_num) (by norm_num) frame hasDistance_two
    state_fibres3.1 state_fibres3.2

noncomputable def resolution6 : RankTwoGlobal.FiniteGeneratorResolution code 6 :=
  SSLPConverse.resolutionOfPair
    (D3NormalizedFiniteToReal.canonicalRoot_primitive 6) angle6_primitive
    (m := 3) (by norm_num) (by norm_num) frame hasDistance_two
    state_fibres6.1 state_fibres6.2

theorem logical_order_three : orderOf resolution3.intrinsicClass = 3 :=
  SSLPConverse.orderOf_intrinsicClass_resolutionOfPair
    (D3NormalizedFiniteToReal.canonicalRoot_primitive 3) angle3_primitive
    (m := 3) (by norm_num) (by norm_num) frame hasDistance_two
    state_fibres3.1 state_fibres3.2

theorem primitive_lift_three :
    GeneralLiftOrder.HasPrimitiveLift code resolution3.intrinsicClass 3 :=
  ⟨inferInstance, angle3, resolution3.intrinsicSymmetry, angle3_primitive, rfl, rfl⟩

theorem minimum_lift_three : GeneralLiftOrder.qMin code (by norm_num)
    resolution3.intrinsicClass = 3 := by
  apply Nat.le_antisymm
  · exact GeneralLiftOrder.qMin_le code (by norm_num) _ (by norm_num) primitive_lift_three
  · have h := GeneralLiftOrder.orderOf_dvd_qMin code (by norm_num) resolution3.intrinsicClass
    rw [logical_order_three] at h
    exact Nat.le_of_dvd (GeneralLiftOrder.qMin_spec code (by norm_num) _).1 h

theorem physical_order_six (k : ℕ) :
    (∀ x, Gate.diag (D3NormalizedFiniteToReal.canonicalRoot 6) angle6 x ^ k = 1) ↔ 6 ∣ k :=
  Gate.pow_eq_one_iff _ (D3NormalizedFiniteToReal.canonicalRoot_primitive 6)
    angle6 angle6_primitive k

theorem physical_order_three (k : ℕ) :
    (∀ x, Gate.diag (D3NormalizedFiniteToReal.canonicalRoot 3) angle3 x ^ k = 1) ↔ 3 ∣ k :=
  Gate.pow_eq_one_iff _ (D3NormalizedFiniteToReal.canonicalRoot_primitive 3)
    angle3 angle3_primitive k

theorem phase_eq_iff (t s : ℝ) :
    phase t = phase s ↔ ∃ z : ℤ, t - s = z := by
  have he : phase (t-s) = phase t / phase s := by
    simp only [phase, Complex.ofReal_sub, mul_sub, Complex.exp_sub]
  rw [← div_eq_one_iff_eq (show phase s ≠ 0 from Complex.exp_ne_zero _), ← he]
  simpa using phase_pow_eq_one_iff (t-s) 1

theorem canonicalRoot_pow (q k : ℕ) :
    D3NormalizedFiniteToReal.canonicalRoot q ^ k = phase ((k : ℝ) / q) := by
  rw [D3NormalizedFiniteToReal.canonicalRoot, ← Complex.exp_nat_mul, phase]
  congr 1
  push_cast
  ring

theorem angle6_values : ∀ j, (angle6 j).val = ![1,1,1,3,5] j := by decide
theorem angle3_values : ∀ j, (angle3 j).val = ![0,1,1,1,0] j := by decide

theorem rational_local6 (j : Fin 5) : phase (theta (1/6) j) =
    D3NormalizedFiniteToReal.canonicalRoot 6 ^ (angle6 j).val := by
  rw [canonicalRoot_pow, angle6_values, phase_eq_iff]
  fin_cases j
  · exact ⟨0, by norm_num [theta]⟩
  · exact ⟨0, by norm_num [theta]⟩
  · exact ⟨0, by norm_num [theta]⟩
  · exact ⟨0, by norm_num [theta]⟩
  · exact ⟨-1, by norm_num [theta]⟩

theorem rational_local3 (j : Fin 5) : phase (theta 0 j) =
    D3NormalizedFiniteToReal.canonicalRoot 3 ^ (angle3 j).val := by
  rw [canonicalRoot_pow, angle3_values, phase_eq_iff]
  fin_cases j <;> exact ⟨0, by norm_num [theta]⟩

theorem rational_gate6 (f : SS.State 5 ℂ) : RealGate.realGate (theta (1/6)) f =
    Gate.gate (D3NormalizedFiniteToReal.canonicalRoot 6) angle6 f := by
  have h := SymmetryToEntrance.realGateEnd_eq_diagonalAction
    (GlobalClassificationBridge.finiteLocalPhase _
      (D3NormalizedFiniteToReal.canonicalRoot_primitive 6) angle6)
    (theta (1/6)) rational_local6 f
  exact h.trans (GlobalClassificationBridge.diagonalAction_finiteLocalPhase _ _ _ _)

theorem rational_gate3 (f : SS.State 5 ℂ) : RealGate.realGate (theta 0) f =
    Gate.gate (D3NormalizedFiniteToReal.canonicalRoot 3) angle3 f := by
  have h := SymmetryToEntrance.realGateEnd_eq_diagonalAction
    (GlobalClassificationBridge.finiteLocalPhase _
      (D3NormalizedFiniteToReal.canonicalRoot_primitive 3) angle3)
    (theta 0) rational_local3 f
  exact h.trans (GlobalClassificationBridge.diagonalAction_finiteLocalPhase _ _ _ _)

theorem least_denominator_six (k : ℕ) :
    (∀ j, ∃ z : ℤ, (k : ℝ) * theta (1/6) j = z) ↔ 6 ∣ k := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := h 0
    have he : (k : ℤ) = 6*z := by
      have : (k : ℝ) = 6*(z : ℝ) := by norm_num [theta] at hz; linarith
      exact_mod_cast this
    exact_mod_cast (show (6 : ℤ) ∣ k from ⟨z, he⟩)
  · rintro ⟨l, rfl⟩ j
    fin_cases j
    · exact ⟨(l : ℤ), by norm_num [theta]; ring⟩
    · exact ⟨(l : ℤ), by norm_num [theta]; ring⟩
    · exact ⟨(l : ℤ), by norm_num [theta]; ring⟩
    · exact ⟨3*(l : ℤ), by norm_num [theta]; ring⟩
    · exact ⟨-(l : ℤ), by norm_num [theta]; ring⟩

theorem family_agrees_on_code (t s : ℝ) (f : SS.State 5 ℂ)
    (hf : f ∈ CodeSpec.codeSpan frame) :
    RealGate.realGate (theta t) f = RealGate.realGate (theta s) f := by
  apply LinearMap.eqOn_span (f := PhaseSectorBridge.realGateEnd (theta t))
    (g := PhaseSectorBridge.realGateEnd (theta s)) ?_ hf
  rintro _ ⟨i, rfl⟩
  exact (eigen_family t i).trans (eigen_family s i).symm

theorem lifts_same_class : resolution6.intrinsicClass = resolution3.intrinsicClass := by
  apply IntrinsicClassBridge.intrinsicClass_eq_of_sameProjective
    (GlobalClassificationBridge.exactCodeProjector code)
    resolution6.intrinsicSymmetry resolution3.intrinsicSymmetry 1 one_ne_zero
  intro f hf
  rw [one_smul]
  have hm := (GlobalClassificationBridge.inProjectorRange_ofFrame_iff frame f).mp hf
  change ClassificationLevels.diagonalAction
      (GlobalClassificationBridge.finiteLocalPhase _ _ angle6) f =
    ClassificationLevels.diagonalAction
      (GlobalClassificationBridge.finiteLocalPhase _ _ angle3) f
  rw [GlobalClassificationBridge.diagonalAction_finiteLocalPhase,
    GlobalClassificationBridge.diagonalAction_finiteLocalPhase]
  change Gate.gate (D3NormalizedFiniteToReal.canonicalRoot 6) angle6 f =
    Gate.gate (D3NormalizedFiniteToReal.canonicalRoot 3) angle3 f
  rw [← rational_gate6, ← rational_gate3]
  exact family_agrees_on_code (1/6) 0 f hm

theorem primitive_lift_six_same_class :
    GeneralLiftOrder.HasPrimitiveLift code resolution3.intrinsicClass 6 :=
  ⟨inferInstance, angle6, resolution6.intrinsicSymmetry,
    angle6_primitive, rfl, lifts_same_class⟩

noncomputable def phaseUnitary (t : ℝ) : unitary ℂ :=
  ⟨phase t, by
    have hn : Complex.normSq (phase t) = 1 := by
      simp [phase, Complex.normSq_eq_norm_sq, Complex.norm_exp,
        Complex.mul_re, Complex.mul_im]
    constructor
    · rw [Complex.star_def, mul_comm, Complex.mul_conj, hn]
      norm_num
    · rw [Complex.star_def, Complex.mul_conj, hn]
      norm_num⟩

noncomputable def familyPhase (t : ℝ) : ClassificationLevels.LocalPhase 5 :=
  fun j => phaseUnitary (theta t j)

theorem familyPhase_action (t : ℝ) (f : SS.State 5 ℂ) :
    ClassificationLevels.diagonalAction (familyPhase t) f =
      RealGate.realGate (theta t) f :=
  (SymmetryToEntrance.realGateEnd_eq_diagonalAction
    (familyPhase t) (theta t) (fun _ => rfl) f).symm

theorem familyPhase_agrees (t : ℝ) (f : SS.State 5 ℂ)
    (hf : ClassificationLevels.InProjectorRange
      (GlobalClassificationBridge.exactCodeProjector code) f) :
    ClassificationLevels.diagonalAction (familyPhase t) f =
      ClassificationLevels.diagonalAction
        (resolution3.intrinsicSymmetry : ClassificationLevels.LocalPhase 5) f := by
  rw [familyPhase_action]
  change _ = ClassificationLevels.diagonalAction
    (GlobalClassificationBridge.finiteLocalPhase _ _ angle3) f
  rw [GlobalClassificationBridge.diagonalAction_finiteLocalPhase]
  change _ = Gate.gate (D3NormalizedFiniteToReal.canonicalRoot 3) angle3 f
  rw [← rational_gate3]
  exact family_agrees_on_code t 0 f
    ((GlobalClassificationBridge.inProjectorRange_ofFrame_iff frame f).mp hf)

theorem familyPhase_preserves (t : ℝ) :
    ClassificationLevels.PreservesProjectorRange
      (GlobalClassificationBridge.exactCodeProjector code) (familyPhase t) := by
  constructor
  · intro f hf
    rw [familyPhase_agrees t f hf]
    exact resolution3.intrinsicSymmetry.property.1 f hf
  · intro f hf
    have hm := resolution3.intrinsicSymmetry.property.2 f hf
    have he := familyPhase_agrees t _ hm
    have hi := congrArg
      (ClassificationLevels.diagonalAction (familyPhase t)⁻¹) he
    rw [ClassificationLevels.diagonalAction_inv_left,
      ClassificationLevels.diagonalAction_inv_right] at hi
    rw [← hi]
    exact hm

/-- The symmetry is the original real physical gate, including irrational t. -/
noncomputable def familySymmetry (t : ℝ) : ClassificationLevels.diagonalSymmetryGroup
    (GlobalClassificationBridge.exactCodeProjector code) :=
  ⟨familyPhase t, familyPhase_preserves t⟩

theorem family_class (t : ℝ) : ClassificationLevels.intrinsicClass
    (GlobalClassificationBridge.exactCodeProjector code) (familySymmetry t) =
    resolution3.intrinsicClass := by
  apply IntrinsicClassBridge.intrinsicClass_eq_of_sameProjective _
    (familySymmetry t) resolution3.intrinsicSymmetry 1 one_ne_zero
  intro f hf
  simpa only [one_smul] using familyPhase_agrees t f hf

theorem family_logical_order (t : ℝ) : orderOf (ClassificationLevels.intrinsicClass
    (GlobalClassificationBridge.exactCodeProjector code) (familySymmetry t)) = 3 := by
  rw [family_class, logical_order_three]

theorem family_minimum_lift (t : ℝ) : GeneralLiftOrder.qMin code (by norm_num)
    (ClassificationLevels.intrinsicClass
      (GlobalClassificationBridge.exactCodeProjector code) (familySymmetry t)) = 3 := by
  rw [family_class, minimum_lift_three]

/-- Both rational replacements lift the original physical family's class. -/
theorem family_rational_lifts (t : ℝ) :
    GeneralLiftOrder.HasPrimitiveLift code
      (ClassificationLevels.intrinsicClass
        (GlobalClassificationBridge.exactCodeProjector code) (familySymmetry t)) 3 ∧
    GeneralLiftOrder.HasPrimitiveLift code
      (ClassificationLevels.intrinsicClass
        (GlobalClassificationBridge.exactCodeProjector code) (familySymmetry t)) 6 := by
  rw [family_class]
  exact ⟨primitive_lift_three, primitive_lift_six_same_class⟩

/-- The example's original irrational physical gate, its exact-distance code,
and both rational lifts refer to one and the same intrinsic logical class. -/
theorem fully_certified (t : ℝ) (ht : Irrational t) :
    SS.HasDistance state 2 ∧ ¬ SS.HasDistance state 3 ∧
    (∀ k : ℕ, 0 < k → (RealGate.realGate (theta t))^[k] ≠ id) ∧
    orderOf (ClassificationLevels.intrinsicClass
      (GlobalClassificationBridge.exactCodeProjector code) (familySymmetry t)) = 3 ∧
    GeneralLiftOrder.qMin code (by norm_num) (ClassificationLevels.intrinsicClass
      (GlobalClassificationBridge.exactCodeProjector code) (familySymmetry t)) = 3 ∧
    GeneralLiftOrder.HasPrimitiveLift code (ClassificationLevels.intrinsicClass
      (GlobalClassificationBridge.exactCodeProjector code) (familySymmetry t)) 6 :=
  ⟨hasDistance_two, not_hasDistance_three, fun _ hk => physical_infinite_order ht hk,
    family_logical_order t, family_minimum_lift t, (family_rational_lifts t).2⟩

end MainTheory.FiveQubitRationalization
