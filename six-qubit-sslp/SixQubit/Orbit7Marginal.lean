import SixQubit.Orbit7UniversalScalar

/-!
# The closing clause of `lem:o7scalarmoments`

The manuscript's scalar normal form ends with "consequently every active qubit
has maximally mixed one-qubit marginal".  `scalar_normal_form` proves the
three displayed equations; this file proves that sentence.

The manuscript's own argument, in its two halves:

* the `Z_i` scalar vanishes because the occupation of an active qubit is
  `5/6 - 1/3 = 1/2` in the bottom word and `1/3 + 1/6 = 1/2` in the top one,
  which is `eq:o7fractionalmatching` read at one vertex;
* "the global order-three symmetry makes the `X_i` and `Y_i` scalars vanish as
  well".  That symmetry is the residue: both words are supported on a single
  class of `weight uniformAv`, and flipping one active coordinate moves the
  residue by a unit of `ZMod 3`, so the two arguments of every off-diagonal
  term lie in different classes and the term is zero.  `weight_flip_ne` is
  that step, and it is a finite check.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators
open SixQubit ComplexConjugate

noncomputable section

/-- The one-qubit reduced density matrix on qubit `i`: the entry `(r, s)` sums
`c(rest, r) * conj (c(rest, s))` over the other five qubits. -/
def oneMarginal (c : SS.State 6 ℂ) (i : Fin 6) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r s =>
    ∑ x ∈ Finset.univ.filter (fun x : SS.BitString 6 => x i = decide (r = 1)),
      c x * conj (c (Function.update x i (decide (s = 1))))

/-- Flipping one coordinate, as an update. -/
theorem update_not_eq_bxor (x : SS.BitString 6) (j : Fin 6) :
    Function.update x j (!(x j)) = SS.bxor x (SS.stdBasis j) := by
  funext i
  by_cases h : i = j
  · subst h
    simp [SS.bxor, SS.stdBasis]
  · have hb : (i == j) = false := by simpa using h
    rw [Function.update_of_ne h]
    simp [SS.bxor, SS.stdBasis, hb]

/-- **The residue moves.**  Flipping an active coordinate changes the
`ZMod 3` residue, so no two strings differing in one active coordinate lie in
the same shell.  This is the content of the manuscript's "global order-three
symmetry" for the off-diagonal one-body scalars. -/
theorem weight_flip_ne (j : Fin 5) (x : SS.BitString 6) :
    SS.weight uniformAv (SS.bxor x (SS.stdBasis j.succ)) ≠ SS.weight uniformAv x := by
  revert j x
  decide

/-- Every off-diagonal entry of an active one-qubit marginal vanishes, for a
word supported on a single residue shell. -/
theorem offdiag_zero {c : SS.State 6 ℂ} {t : ZMod 3}
    (hc : ∀ x, SS.weight uniformAv x ≠ t → c x = 0) (j : Fin 5) (b : Bool) :
    (∑ x ∈ Finset.univ.filter (fun x : SS.BitString 6 => x j.succ = b),
      c x * conj (c (Function.update x j.succ (!b)))) = 0 := by
  refine Finset.sum_eq_zero fun x hx => ?_
  have hxb : x j.succ = b := (Finset.mem_filter.1 hx).2
  by_cases h0 : SS.weight uniformAv x = t
  · have hup : Function.update x j.succ (!b) = SS.bxor x (SS.stdBasis j.succ) := by
      rw [← hxb]
      exact update_not_eq_bxor x j.succ
    have hne : SS.weight uniformAv (SS.bxor x (SS.stdBasis j.succ)) ≠ t := by
      rw [← h0]
      exact weight_flip_ne j x
    rw [hup, hc _ hne, map_zero, mul_zero]
  · rw [hc x h0, zero_mul]

/-- Restricting a sum of squared moduli to the support. -/
theorem sum_univ_filter_eq {c : SS.State 6 ℂ} {S : Finset (SS.BitString 6)}
    (hc : ∀ x, x ∉ S → c x = 0) (P : SS.BitString 6 → Prop)
    [DecidablePred P] :
    (∑ x ∈ Finset.univ.filter P, Complex.normSq (c x))
      = ∑ x ∈ S.filter P, Complex.normSq (c x) := by
  refine (Finset.sum_subset ?_ ?_).symm
  · exact Finset.filter_subset_filter P (Finset.subset_univ S)
  · intro x hx hxs
    have hP : P x := (Finset.mem_filter.1 hx).2
    have : x ∉ S := fun h => hxs (Finset.mem_filter.2 ⟨h, hP⟩)
    rw [hc x this, map_zero]

/-- A diagonal entry of the marginal is an occupation number. -/
theorem oneMarginal_diag (c : SS.State 6 ℂ) (i : Fin 6) (r : Fin 2) :
    oneMarginal c i r r
      = ((∑ x ∈ Finset.univ.filter
          (fun x : SS.BitString 6 => x i = decide (r = 1)), Complex.normSq (c x) : ℝ) : ℂ) := by
  rw [oneMarginal]
  simp only [Matrix.of_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hxi : x i = decide (r = 1) := (Finset.mem_filter.1 hx).2
  rw [← hxi, Function.update_eq_self, Complex.mul_conj]

/-- **The closing clause of `lem:o7scalarmoments`.**

Every active qubit of an exact orbit-7 solution has maximally mixed one-qubit
marginal, in both logical words. -/
theorem active_marginal_maximally_mixed (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c, d] 3) (i : Fin 5) :
    oneMarginal c i.succ = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      oneMarginal d i.succ = (1 / 2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨hu, hv, hAt, hBt, hdeg, _⟩ := scalar_normal_form c d hc hd hnc hnd hcode
  have hcS := full_support0 hc
  have hdS := full_support2 hd
  -- the two occupation numbers are both `1/2`
  have hoccC : occOn S0 c i.succ = 1 / 2 := by
    rw [occ0_formula, hAt, (hdeg i).1]
    norm_num
  have hoccD : occOn S2 d i.succ = 1 / 2 := by
    rw [occ2_formula, hv, (hdeg i).2]
    norm_num
  -- and the total masses are one
  have hmC : massOn S0 c = 1 := by
    have := (innerC_self_eq_massOn S0 c hcS).symm.trans hnc
    exact_mod_cast this
  have hmD : massOn S2 d = 1 := by
    have := (innerC_self_eq_massOn S2 d hdS).symm.trans hnd
    exact_mod_cast this
  -- the complementary occupation is also `1/2`
  have hsplitC : (∑ x ∈ S0.filter (fun x => x i.succ = false), Complex.normSq (c x))
      = 1 / 2 := by
    have hsum : (∑ x ∈ S0.filter (fun x => x i.succ = true), Complex.normSq (c x))
        + ∑ x ∈ S0.filter (fun x => ¬ (x i.succ = true)), Complex.normSq (c x)
          = massOn S0 c := Finset.sum_filter_add_sum_filter_not _ _ _
    rw [hmC] at hsum
    have hocc : (∑ x ∈ S0.filter (fun x => x i.succ = true), Complex.normSq (c x))
        = 1 / 2 := hoccC
    have hcongr : (S0.filter (fun x => ¬ (x i.succ = true)))
        = S0.filter (fun x => x i.succ = false) := by
      apply Finset.filter_congr
      intro x _
      simp
    rw [hocc, hcongr] at hsum
    linarith
  have hsplitD : (∑ x ∈ S2.filter (fun x => x i.succ = false), Complex.normSq (d x))
      = 1 / 2 := by
    have hsum : (∑ x ∈ S2.filter (fun x => x i.succ = true), Complex.normSq (d x))
        + ∑ x ∈ S2.filter (fun x => ¬ (x i.succ = true)), Complex.normSq (d x)
          = massOn S2 d := Finset.sum_filter_add_sum_filter_not _ _ _
    rw [hmD] at hsum
    have hocc : (∑ x ∈ S2.filter (fun x => x i.succ = true), Complex.normSq (d x))
        = 1 / 2 := hoccD
    have hcongr : (S2.filter (fun x => ¬ (x i.succ = true)))
        = S2.filter (fun x => x i.succ = false) := by
      apply Finset.filter_congr
      intro x _
      simp
    rw [hocc, hcongr] at hsum
    linarith
  have hoccC' : (∑ x ∈ S0.filter (fun x => x i.succ = true), Complex.normSq (c x))
      = 1 / 2 := hoccC
  have hoccD' : (∑ x ∈ S2.filter (fun x => x i.succ = true), Complex.normSq (d x))
      = 1 / 2 := hoccD
  have c00 : oneMarginal c i.succ 0 0 = 1 / 2 := by
    rw [oneMarginal_diag, sum_univ_filter_eq hcS]
    norm_num [hsplitC]
  have c11 : oneMarginal c i.succ 1 1 = 1 / 2 := by
    rw [oneMarginal_diag, sum_univ_filter_eq hcS]
    norm_num [hoccC']
  have c01 : oneMarginal c i.succ 0 1 = 0 := by
    simpa [oneMarginal] using offdiag_zero hc i false
  have c10 : oneMarginal c i.succ 1 0 = 0 := by
    simpa [oneMarginal] using offdiag_zero hc i true
  have d00 : oneMarginal d i.succ 0 0 = 1 / 2 := by
    rw [oneMarginal_diag, sum_univ_filter_eq hdS]
    norm_num [hsplitD]
  have d11 : oneMarginal d i.succ 1 1 = 1 / 2 := by
    rw [oneMarginal_diag, sum_univ_filter_eq hdS]
    norm_num [hoccD']
  have d01 : oneMarginal d i.succ 0 1 = 0 := by
    simpa [oneMarginal] using offdiag_zero hd i false
  have d10 : oneMarginal d i.succ 1 0 = 0 := by
    simpa [oneMarginal] using offdiag_zero hd i true
  constructor
  · ext r s
    fin_cases r <;> fin_cases s
    · simpa using c00
    · simpa using c01
    · simpa using c10
    · simpa using c11
  · ext r s
    fin_cases r <;> fin_cases s
    · simpa using d00
    · simpa using d01
    · simpa using d10
    · simpa using d11

end

end SixQubit.Orbit7Universal
