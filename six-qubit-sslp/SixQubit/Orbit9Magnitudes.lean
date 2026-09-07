import SixQubit.Orbit9MagnitudeMoments

/-!
# The universal orbit-9 magnitude pattern

The inactive equal-bit pair saturates the entire weight-two Pauli budget.
The remaining diagonal Pauli coefficients and full-fiber occupation formulas
then force all singleton and edge probabilities, with no phase assumption.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate
open SS.MacWilliams

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def magnitudeZZ (i j : Fin 6) : SS.PauliString 6 :=
  ⟨fun _ => false, SS.bxor (SS.stdBasis i) (SS.stdBasis j)⟩

theorem magnitudeZZ_eq_iff (i j a b : Fin 6) (hij : i ≠ j) (hab : a ≠ b) :
    magnitudeZZ i j = magnitudeZZ a b ↔ (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  constructor
  · intro h
    have hf : ∀ i j a b : Fin 6, i ≠ j → a ≠ b →
        (∀ k, SS.bxor (SS.stdBasis i) (SS.stdBasis j) k =
          SS.bxor (SS.stdBasis a) (SS.stdBasis b) k) →
          (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by decide
    exact hf i j a b hij hab (fun k => congrArg (fun P => P.z k) h)
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · rfl
    · simp [magnitudeZZ, SS.bxor_comm]

theorem trace_zero_of_single_saturation (psi : Fin 2 → SS.State 6 ℂ)
    (G P : SS.PauliString 6) (hG : G.wt = 2) (hP : P.wt = 2)
    (hne : P ≠ G) (htr : trProj psi G = 2) (hA : Aco psi 2 = 4) :
    trProj psi P = 0 := by
  classical
  let W := Finset.univ.filter (fun Q : SS.PauliString 6 => Q.wt = 2)
  let f := fun Q => Complex.normSq (trProj psi Q)
  have hGmem : G ∈ W := by simp [W, hG]
  have hsplit := Finset.sum_erase_add W f hGmem
  have hsum : (∑ Q ∈ W, f Q) = 4 := hA
  have hfG : f G = 4 := by norm_num [f, htr, Complex.normSq]
  have hz : (∑ Q ∈ W.erase G, f Q) = 0 := by linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun Q _ => Complex.normSq_nonneg (trProj psi Q))).mp hz
  exact Complex.normSq_eq_zero.mp (hall P (by simp [W, hP, hne]))

theorem equal_pair_trace (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hc : EqualBitsSupport c a b) (hd : EqualBitsSupport d a b) :
    trProj ![c,d] (magnitudeZZ a b) = 2 := by
  have hfc := zpair_fixes_of_equalBits c a b hc
  have hfd := zpair_fixes_of_equalBits d a b hd
  simp only [trProj, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, magnitudeZZ, hfc, hfd, H.norm0, H.norm1]
  norm_num

/-- All other weight-two Paulis have zero scalar. -/
theorem other_weightTwo_trace_zero (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hab : a ≠ b)
    (hc : EqualBitsSupport c a b) (hd : EqualBitsSupport d a b)
    (P : SS.PauliString 6) (hP : P.wt = 2) (hne : P ≠ magnitudeZZ a b) :
    trProj ![c,d] P = 0 := by
  have hA := (enumerator_of_equal_pair c d H.norm0 H.norm1 H.distance
    a b hab hc hd).1
  exact trace_zero_of_single_saturation ![c,d] (magnitudeZZ a b) P
    (zpair_wt a b hab) hP hne (equal_pair_trace c d H a b hc hd) hA.2.2.1

/-- Exact relation between the physical `ZZ` trace and edge probabilities. -/
theorem magnitudeZZ_trace_real (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j : Fin 6) (hij : i ≠ j) :
    (trProj ![c,d] (magnitudeZZ i j)).re =
      2/3 - 8*p c i - 8*p c j + 8*r c i j := by
  have hchar := SixQubit.charOn_eq_of_hasDistance S0 S1 c d H.support0 H.support1
    H.distance (SS.bxor (SS.stdBasis i) (SS.stdBasis j))
    (by rw [zpair_wt i j hij])
  simp only [trProj, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, magnitudeZZ]
  rw [SixQubit.innerC_pureZ_eq_charOn S0 c H.support0,
    SixQubit.innerC_pureZ_eq_charOn S1 d H.support1, ← hchar]
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [SixQubit.charOn_stdBasis_pair,
    SixQubit.massOn_eq_one S0 c H.support0 H.norm0,
    occOn_S0_formula, occOn_S0_formula, occ2_S0_magnitudes c i j hij]
  have hm := (global_masses c d H.support0 H.support1 H.norm0 H.norm1 H.distance).2.1
  have hi := (pq_degree c d H.support0 H.support1 H.norm0 H.norm1 H.distance i).2.1
  have hj := (pq_degree c d H.support0 H.support1 H.norm0 H.norm1 H.distance j).2.1
  linarith

theorem equal_pair_singleton_zero (c : SS.State 6 ℂ) (a b : Fin 6)
    (hab : a ≠ b) (hc : EqualBitsSupport c a b) : p c a = 0 ∧ p c b = 0 := by
  have ha : one a a ≠ one a b := by
    rw [one_eq_stdBasis, SS.stdBasis_apply_self, SS.stdBasis_apply_ne (Ne.symm hab)]
    decide
  have hb : one b a ≠ one b b := by
    rw [one_eq_stdBasis, SS.stdBasis_apply_ne hab, SS.stdBasis_apply_self]
    decide
  simp [p, hc (one a) ha, hc (one b) hb]

theorem equal_pair_cross_zero (c : SS.State 6 ℂ) (a b i : Fin 6)
    (hab : a ≠ b) (hia : i ≠ a) (hib : i ≠ b)
    (hc : EqualBitsSupport c a b) : r c i a = 0 := by
  have hbits : SS.complement (pair i a) a ≠ SS.complement (pair i a) b := by
    have hf : ∀ i a b : Fin 6, a ≠ b → i ≠ a → i ≠ b →
        SS.complement (pair i a) a ≠ SS.complement (pair i a) b := by decide
    exact hf i a b hab hia hib
  simp [r, hia, hc _ hbits]

/-- Inactive singleton probabilities vanish and the other four are `1/12`. -/
theorem singleton_magnitude_formula_of_equal_pair
    (c d : SS.State 6 ℂ) (H : FullKL c d) (a b : Fin 6) (hab : a ≠ b)
    (hc : EqualBitsSupport c a b) (hd : EqualBitsSupport d a b) (i : Fin 6) :
    p c i = if i = a ∨ i = b then 0 else 1/12 := by
  have hp := equal_pair_singleton_zero c a b hab hc
  by_cases hi : i = a ∨ i = b
  · rw [if_pos hi]
    rcases hi with rfl | rfl
    · exact hp.1
    · exact hp.2
  · rw [if_neg hi]
    push_neg at hi
    have hr := equal_pair_cross_zero c a b i hab hi.1 hi.2 hc
    have hn : magnitudeZZ i a ≠ magnitudeZZ a b := by
      rw [ne_eq, magnitudeZZ_eq_iff i a a b hi.1 hab]
      simp [hi.1, hi.2]
    have ht := other_weightTwo_trace_zero c d H a b hab hc hd
      (magnitudeZZ i a) (zpair_wt i a hi.1) hn
    have hrel := magnitudeZZ_trace_real c d H i a hi.1
    rw [ht, Complex.zero_re, hp.1, hr] at hrel
    linarith

/-- The displayed edge-probability pattern, including every omitted zero. -/
def expectedEdgeMagnitude (a b i j : Fin 6) : ℝ :=
  if i = j then 0 else
    if i = a ∨ i = b then
      if j = a ∨ j = b then 1/6 else 0
    else if j = a ∨ j = b then 0 else 1/12

theorem edge_magnitude_formula_of_equal_pair
    (c d : SS.State 6 ℂ) (H : FullKL c d) (a b : Fin 6) (hab : a ≠ b)
    (hc : EqualBitsSupport c a b) (hd : EqualBitsSupport d a b) (i j : Fin 6) :
    r c i j = expectedEdgeMagnitude a b i j := by
  by_cases hij : i = j
  · subst j
    simp [r, expectedEdgeMagnitude]
  have hpi := singleton_magnitude_formula_of_equal_pair c d H a b hab hc hd i
  have hpj := singleton_magnitude_formula_of_equal_pair c d H a b hab hc hd j
  have hrel := magnitudeZZ_trace_real c d H i j hij
  have hiff : magnitudeZZ i j = magnitudeZZ a b ↔
      (i = a ∨ i = b) ∧ (j = a ∨ j = b) := by
    rw [magnitudeZZ_eq_iff i j a b hij hab]
    constructor
    · tauto
    · rintro ⟨hi,hj⟩
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all
  by_cases hi : i = a ∨ i = b <;> by_cases hj : j = a ∨ j = b
  · have ht := equal_pair_trace c d H a b hc hd
    rw [hiff.mpr ⟨hi,hj⟩, ht] at hrel
    simp only [if_pos hi, if_pos hj] at hpi hpj
    simp only [expectedEdgeMagnitude, if_neg hij, if_pos hi, if_pos hj]
    norm_num at hrel
    linarith
  all_goals
    have hne : magnitudeZZ i j ≠ magnitudeZZ a b := by rw [ne_eq, hiff]; tauto
    have ht := other_weightTwo_trace_zero c d H a b hab hc hd
      (magnitudeZZ i j) (zpair_wt i j hij) hne
    rw [ht, Complex.zero_re] at hrel
    simp only [hi, hj, ↓reduceIte] at hpi hpj
    simp only [expectedEdgeMagnitude, if_neg hij, hi, hj, ↓reduceIte]
    linarith

/-- An explicit pattern on the original six coordinate labels.  This states
the four active singleton magnitudes, six active edges, inactive edge, and
all cross-edge and inactive-singleton zeros for both logical words. -/
structure MagnitudePattern (c d : SS.State 6 ℂ) (a b : Fin 6) : Prop where
  distinct : a ≠ b
  singleton : ∀ i, p c i = (if i = a ∨ i = b then 0 else 1/12) ∧
    q d i = (if i = a ∨ i = b then 0 else 1/12)
  edge : ∀ i j, r c i j = expectedEdgeMagnitude a b i j ∧
    s d i j = expectedEdgeMagnitude a b i j

theorem magnitudePattern_of_equal_pair
    (c d : SS.State 6 ℂ) (H : FullKL c d) (a b : Fin 6) (hab : a ≠ b)
    (hc : EqualBitsSupport c a b) (hd : EqualBitsSupport d a b) :
    MagnitudePattern c d a b := by
  refine ⟨hab, ?_, ?_⟩
  · intro i
    have hp := singleton_magnitude_formula_of_equal_pair c d H a b hab hc hd i
    have he := pq_equal c d H.support0 H.support1 H.norm0 H.norm1 H.distance i
    exact ⟨hp, he.symm.trans hp⟩
  · intro i j
    have hr := edge_magnitude_formula_of_equal_pair c d H a b hab hc hd i j
    exact ⟨hr, (edge_magnitudes_equal c d H i j).symm.trans hr⟩

/-- The supplementary magnitude corollary for arbitrary full uniform fibers. -/
theorem universal_magnitude_pattern (c d : SS.State 6 ℂ) (H : FullKL c d) :
    ∃ a b : Fin 6, MagnitudePattern c d a b := by
  have hfour := active_card_eq_four_of_ne_two c d H (active_card_ne_two c d H)
  obtain ⟨a,b,hab,hc,hd⟩ := equal_pair_of_card_four c d H hfour
  exact ⟨a,b,magnitudePattern_of_equal_pair c d H a b hab hc hd⟩

/-- Original-gauge full-fiber input; the conclusion is in the manuscript's
uniform gauge, obtained by the actual sixth-qubit bit flip. -/
theorem original_magnitude_pattern (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    ∃ a b : Fin 6, MagnitudePattern (toUniform c) (toUniform d) a b := by
  apply universal_magnitude_pattern
  exact {
    support0 := toUniform_support0 c hc
    support1 := toUniform_support1 d hd
    norm0 := (innerC_toUniform c c).trans hnc
    norm1 := (innerC_toUniform d d).trans hnd
    distance := hasDistance_toUniform c d hdist }

end
end SixQubit.Orbit9Universal
