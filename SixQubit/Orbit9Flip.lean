import SixQubit.Orbit9Universal

/-!
# Orbit 9: the single-flip Walsh reduction

This file extracts the exact complex single-flip equations directly from the
off-diagonal Knill--Laflamme rows.  The sums run over the complete orbit-9
fibres; no displayed witness support is assumed.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate

noncomputable section

def zero6 : SS.BitString 6 := fun _ => false

def epsO9 (b : Bool) : ℤ := if b then -1 else 1

@[simp] lemma epsO9_false : epsO9 false = 1 := rfl
@[simp] lemma epsO9_true : epsO9 true = -1 := rfl

lemma signMul_eq_epsO9 (b : Bool) (u : ℂ) :
    SixQubit.signMul b u = (epsO9 b : ℂ) * u := by
  cases b <;> simp [epsO9, SixQubit.signMul]

@[simp] lemma bdot_zero6 (y : SS.BitString 6) :
    SS.bdot zero6 y = false := by
  simp [zero6, SS.bdot]

def flipInter (i : Fin 6) : Finset (SS.BitString 6) :=
  S1.filter (fun y => SS.bxor y (SS.stdBasis i) ∈ S0)

def flipTerm (c d : SS.State 6 ℂ) (i : Fin 6)
    (y : SS.BitString 6) : ℂ :=
  star (c (SS.bxor y (SS.stdBasis i))) * d y

def flipLow (c d : SS.State 6 ℂ) (i : Fin 6) : ℂ :=
  ∑ y ∈ flipInter i,
    if hwt y = 2 then flipTerm c d i y else 0

def flipHigh (c d : SS.State 6 ℂ) (i : Fin 6) : ℂ :=
  ∑ y ∈ flipInter i,
    if hwt y = 5 then flipTerm c d i y else 0

theorem flipInter_weights : ∀ i : Fin 6, ∀ y : SS.BitString 6,
    y ∈ flipInter i → hwt y = 2 ∨ hwt y = 5 := by
  decide

lemma offSum_zero_expansion (c d : SS.State 6 ℂ) (i : Fin 6) :
    SixQubit.offSumOn S0 S1 c d (SS.stdBasis i) zero6 =
      flipLow c d i + flipHigh c d i := by
  classical
  unfold SixQubit.offSumOn flipLow flipHigh flipInter flipTerm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  have hw := flipInter_weights i y hy
  rcases hw with hw | hw
  · simp [hw]
  · simp [hw]

/-- Sum of the five one-coordinate Walsh signs on a reciprocal incidence.
Low-shell incidences have coefficient `+3`, high-shell incidences `-3`. -/
theorem flip_walsh_sum_coefficient : ∀ i : Fin 6, ∀ y : SS.BitString 6,
    y ∈ S1 → SS.bxor y (SS.stdBasis i) ∈ S0 →
    (∑ j ∈ Finset.univ.erase i,
      epsO9 (SS.bdot (SS.stdBasis j) y)) =
        if hwt y = 2 then 3 else -3 := by
  decide

lemma offSum_dressed_aggregate (c d : SS.State 6 ℂ) (i : Fin 6) :
    (∑ j ∈ Finset.univ.erase i,
      SixQubit.offSumOn S0 S1 c d (SS.stdBasis i) (SS.stdBasis j)) =
        3 * flipLow c d i - 3 * flipHigh c d i := by
  classical
  unfold SixQubit.offSumOn
  rw [Finset.sum_comm]
  calc
    (∑ y ∈ flipInter i,
        ∑ j ∈ Finset.univ.erase i,
          SixQubit.signMul (SS.bdot (SS.stdBasis j) y)
            (flipTerm c d i y)) =
        ∑ y ∈ flipInter i,
          if hwt y = 2 then 3 * flipTerm c d i y
          else -3 * flipTerm c d i y := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      simp_rw [signMul_eq_epsO9]
      rw [← Finset.sum_mul]
      have hc := flip_walsh_sum_coefficient i y
        (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
      have hc' : (∑ j ∈ Finset.univ.erase i,
          (epsO9 (SS.bdot (SS.stdBasis j) y) : ℂ)) =
          if hwt y = 2 then 3 else -3 := by
        exact_mod_cast hc
      rw [hc']
      split <;> ring
    _ = 3 * flipLow c d i - 3 * flipHigh c d i := by
      unfold flipLow flipHigh
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hw := flipInter_weights i y hy
      rcases hw with hw | hw
      · simp [hw]
      · simp [hw]

theorem flip_walsh_single_coefficient : ∀ i j : Fin 6,
    j ≠ i → ∀ y : SS.BitString 6,
    y ∈ S1 → SS.bxor y (SS.stdBasis i) ∈ S0 →
    epsO9 (SS.bdot (SS.stdBasis j) y) =
      (if hwt y = 2 then 1 else -1) +
      (if y = pair i j then -2 else 0) +
      (if y = SS.complement (one j) then 2 else 0) := by
  decide

lemma flip_base_sum (c d : SS.State 6 ℂ) (i : Fin 6) :
    (∑ y ∈ flipInter i,
      if hwt y = 2 then flipTerm c d i y else -flipTerm c d i y) =
        flipLow c d i - flipHigh c d i := by
  classical
  unfold flipLow flipHigh
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  have hw := flipInter_weights i y hy
  rcases hw with hw | hw
  · simp [hw]
  · simp [hw]

theorem pair_mem_flipInter : ∀ i j : Fin 6, j ≠ i →
    pair i j ∈ flipInter i := by
  decide

theorem complement_one_mem_flipInter : ∀ i j : Fin 6, j ≠ i →
    SS.complement (one j) ∈ flipInter i := by
  decide

theorem pair_flip_xor : ∀ i j : Fin 6, j ≠ i →
    SS.bxor (pair i j) (SS.stdBasis i) = one j := by
  decide

theorem complement_one_flip_xor : ∀ i j : Fin 6, j ≠ i →
    SS.bxor (SS.complement (one j)) (SS.stdBasis i) =
      SS.complement (pair i j) := by
  decide

lemma sum_indicator {F : Finset (SS.BitString 6)}
    (t : SS.BitString 6) (ht : t ∈ F)
    (f : SS.BitString 6 → ℂ) (a : ℂ) :
    (∑ y ∈ F, if y = t then a * f y else 0) = a * f t := by
  rw [Finset.sum_eq_single_of_mem t ht]
  · simp
  · intro b hb hbt
    simp [hbt]

/-- A single dressed row, after the two shell sums have been separated,
isolates exactly one low-shell and one high-shell reciprocal incidence. -/
lemma offSum_dressed_expansion (c d : SS.State 6 ℂ) (i j : Fin 6)
    (hji : j ≠ i) :
    SixQubit.offSumOn S0 S1 c d (SS.stdBasis i) (SS.stdBasis j) =
      flipLow c d i - flipHigh c d i
      - 2 * (star (c (one j)) * d (pair i j))
      + 2 * (star (c (SS.complement (pair i j))) *
        d (SS.complement (one j))) := by
  classical
  unfold SixQubit.offSumOn
  change (∑ y ∈ flipInter i,
    SixQubit.signMul (SS.bdot (SS.stdBasis j) y) (flipTerm c d i y)) = _
  calc
    (∑ y ∈ flipInter i,
      SixQubit.signMul (SS.bdot (SS.stdBasis j) y) (flipTerm c d i y)) =
        ∑ y ∈ flipInter i,
          ((if hwt y = 2 then flipTerm c d i y else -flipTerm c d i y) +
          (if y = pair i j then -2 * flipTerm c d i y else 0) +
          (if y = SS.complement (one j) then 2 * flipTerm c d i y else 0)) := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [signMul_eq_epsO9]
      have hc := flip_walsh_single_coefficient i j hji y
        (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2
      have hc' : (epsO9 (SS.bdot (SS.stdBasis j) y) : ℂ) =
          (if hwt y = 2 then 1 else -1) +
          (if y = pair i j then -2 else 0) +
          (if y = SS.complement (one j) then 2 else 0) := by
        exact_mod_cast hc
      rw [hc']
      split_ifs <;> ring
    _ = flipLow c d i - flipHigh c d i
        - 2 * (star (c (one j)) * d (pair i j))
        + 2 * (star (c (SS.complement (pair i j))) *
          d (SS.complement (one j))) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [flip_base_sum]
      rw [sum_indicator (pair i j) (pair_mem_flipInter i j hji)
        (flipTerm c d i) (-2)]
      rw [sum_indicator (SS.complement (one j))
        (complement_one_mem_flipInter i j hji) (flipTerm c d i) 2]
      unfold flipTerm
      rw [pair_flip_xor i j hji, complement_one_flip_xor i j hji]
      ring

theorem flip_wt_zero : ∀ i : Fin 6,
    (⟨SS.stdBasis i, zero6⟩ : SS.PauliString 6).wt ≤ 2 := by
  decide

theorem flip_wt_dressed : ∀ i j : Fin 6,
    (⟨SS.stdBasis i, SS.stdBasis j⟩ : SS.PauliString 6).wt ≤ 2 := by
  decide

/-- The undressed row and the aggregate of all five dressed rows separately
kill the low- and high-shell incidence sums. -/
theorem single_flip_shell_sums (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    flipLow c d i = 0 ∧ flipHigh c d i = 0 := by
  have h0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    (SS.stdBasis i) zero6 (flip_wt_zero i)
  rw [offSum_zero_expansion] at h0
  have hz : (∑ j ∈ Finset.univ.erase i,
      SixQubit.offSumOn S0 S1 c d (SS.stdBasis i) (SS.stdBasis j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (SS.stdBasis i) (SS.stdBasis j) (flip_wt_dressed i j)
  rw [offSum_dressed_aggregate] at hz
  constructor
  · linear_combination (1 / 2) * h0 + (1 / 6) * hz
  · linear_combination (1 / 2) * h0 - (1 / 6) * hz

/-- Exact single-flip normal form, valid for arbitrary amplitudes on the two
complete fibres. -/
theorem single_flip_edge (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) (i j : Fin 6) (hji : j ≠ i) :
    star (c (one j)) * d (pair i j) =
      star (c (SS.complement (pair i j))) * d (SS.complement (one j)) := by
  rcases single_flip_shell_sums c d hc hd hdist i with ⟨hL,hH⟩
  have he := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
    (SS.stdBasis i) (SS.stdBasis j) (flip_wt_dressed i j)
  rw [offSum_dressed_expansion c d i j hji, hL, hH] at he
  linear_combination (-1 / 2) * he

theorem edge_balance (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) (i j : Fin 6) (hji : j ≠ i) :
    p c j * s d i j = q d j * r c i j := by
  have he := single_flip_edge c d hc hd hdist i j hji
  have hn := congrArg Complex.normSq he
  simpa [p, q, r, s, hji, Ne.symm hji, Complex.normSq_mul,
    Complex.star_def, mul_comm] using hn

theorem degree_balance (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    p c i * Sdeg d i = q d i * Rdeg c i := by
  classical
  unfold Sdeg Rdeg
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    simp [r, s]
  · have hb := edge_balance c d hc hd hdist j i (Ne.symm hji)
    rw [s_symm d j i, r_symm c j i] at hb
    exact hb

/-- The single-flip rows remove the last freedom in the diagonal moment
normal form: complementary singleton probabilities coincide coordinatewise. -/
theorem pq_equal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    p c i = q d i := by
  rcases degree_normal_form c d hc hd hnc hnd hdist i with ⟨hR,hS⟩
  have hb := degree_balance c d hc hd hdist i
  rw [hR, hS] at hb
  have hf : (p c i - q d i) * (1 + 9 * p c i + 9 * q d i) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hf with h | h
  · linarith
  · have hp := p_nonneg c i
    have hq := q_nonneg d i
    nlinarith

theorem pq_degree (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    p c i = q d i ∧ Rdeg c i = 1/6 + p c i ∧
      Sdeg d i = 1/6 + p c i := by
  have hpq := pq_equal c d hc hd hnc hnd hdist i
  rcases degree_normal_form c d hc hd hnc hnd hdist i with ⟨hR,hS⟩
  constructor
  · exact hpq
  constructor <;> nlinarith

end

end SixQubit.Orbit9Universal
