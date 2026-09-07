import SixQubit.Orbit9Magnitudes

/-! The corollary's coefficient multiplicities, as counts of actual computational
basis amplitudes on the entire six-qubit cube. -/

namespace SixQubit.Orbit9Universal

open scoped BigOperators
noncomputable section

set_option maxHeartbeats 4000000

theorem magnitude_distribution_S0 (c d : SS.State 6 ℂ) (a b : Fin 6)
    (M : MagnitudePattern c d a b) (F : ℝ → ℝ) :
    (∑ x ∈ S0, F (Complex.normSq (c x))) =
      10 * F (1/12) + F (1/6) + 10 * F 0 := by
  have hp (i : Fin 6) : Complex.normSq (c (one i)) =
      (if i = a ∨ i = b then 0 else 1/12) := (M.singleton i).1
  have hr (i j : Fin 6) (hij : i ≠ j) :
      Complex.normSq (c (SS.complement (pair i j))) = expectedEdgeMagnitude a b i j := by
    simpa only [r, if_neg hij] using (M.edge i j).1
  rw [sum_S0]
  simp_rw [hp, hr 0 1 (by decide), hr 0 2 (by decide), hr 0 3 (by decide), hr 0 4 (by decide), hr 0 5 (by decide), hr 1 2 (by decide), hr 1 3 (by decide), hr 1 4 (by decide), hr 1 5 (by decide), hr 2 3 (by decide), hr 2 4 (by decide), hr 2 5 (by decide), hr 3 4 (by decide), hr 3 5 (by decide), hr 4 5 (by decide)]
  have hab := M.distinct
  fin_cases a <;> fin_cases b
  all_goals try exact (hab rfl).elim
  all_goals
    norm_num [expectedEdgeMagnitude, Fin.ext_iff]
    ring

theorem magnitude_distribution_S1 (c d : SS.State 6 ℂ) (a b : Fin 6)
    (M : MagnitudePattern c d a b) (F : ℝ → ℝ) :
    (∑ x ∈ S1, F (Complex.normSq (d x))) =
      10 * F (1/12) + F (1/6) + 10 * F 0 := by
  have hp (i : Fin 6) : Complex.normSq (d (SS.complement (one i))) =
      (if i = a ∨ i = b then 0 else 1/12) := (M.singleton i).2
  have hr (i j : Fin 6) (hij : i ≠ j) :
      Complex.normSq (d (pair i j)) = expectedEdgeMagnitude a b i j := by
    simpa only [s, if_neg hij] using (M.edge i j).2
  rw [sum_S1]
  simp_rw [hp, hr 0 1 (by decide), hr 0 2 (by decide), hr 0 3 (by decide), hr 0 4 (by decide), hr 0 5 (by decide), hr 1 2 (by decide), hr 1 3 (by decide), hr 1 4 (by decide), hr 1 5 (by decide), hr 2 3 (by decide), hr 2 4 (by decide), hr 2 5 (by decide), hr 3 4 (by decide), hr 3 5 (by decide), hr 4 5 (by decide)]
  have hab := M.distinct
  fin_cases a <;> fin_cases b
  all_goals try exact (hab rfl).elim
  all_goals
    norm_num [expectedEdgeMagnitude, Fin.ext_iff]
    ring

theorem magnitude_count_on_univ (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (M : MagnitudePattern c d a b) (t : ℝ) (ht : t ≠ 0) :
    ((Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (c x) = t)).card : ℝ) =
      10 * (if (1/12 : ℝ) = t then 1 else 0) + (if (1/6 : ℝ) = t then 1 else 0) ∧
    ((Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (d x) = t)).card : ℝ) =
      10 * (if (1/12 : ℝ) = t then 1 else 0) + (if (1/6 : ℝ) = t then 1 else 0) := by
  classical
  have hc : Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (c x) = t) =
      S0.filter (fun x => Complex.normSq (c x) = t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨?_,hx⟩
      by_contra hnot
      rw [H.support0 x hnot, Complex.normSq_zero] at hx
      exact ht hx.symm
    · exact And.right
  have hd : Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (d x) = t) =
      S1.filter (fun x => Complex.normSq (d x) = t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨?_,hx⟩
      by_contra hnot
      rw [H.support1 x hnot, Complex.normSq_zero] at hx
      exact ht hx.symm
    · exact And.right
  rw [hc, hd]
  have h0 := magnitude_distribution_S0 c d a b M
    (fun z => if z = t then (1 : ℝ) else 0)
  have h1 := magnitude_distribution_S1 c d a b M
    (fun z => if z = t then (1 : ℝ) else 0)
  simpa [Ne.symm ht] using And.intro h0 h1

/-- Each logical word has exactly ten coefficients of squared magnitude
`1/12` and exactly one of squared magnitude `1/6`. -/
def ElevenCoefficientPattern (c d : SS.State 6 ℂ) : Prop :=
  (Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (c x) = 1/12)).card = 10 ∧
  (Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (c x) = 1/6)).card = 1 ∧
  (Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (d x) = 1/12)).card = 10 ∧
  (Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (d x) = 1/6)).card = 1

theorem eleven_coefficient_pattern (c d : SS.State 6 ℂ) (H : FullKL c d) :
    ElevenCoefficientPattern c d := by
  obtain ⟨a,b,M⟩ := universal_magnitude_pattern c d H
  have h12 := magnitude_count_on_univ c d H a b M (1/12) (by norm_num)
  have h6 := magnitude_count_on_univ c d H a b M (1/6) (by norm_num)
  norm_num at h12 h6
  refine ⟨?_,?_,?_,?_⟩
  · exact_mod_cast h12.1
  · exact_mod_cast h6.1
  · exact_mod_cast h12.2
  · exact_mod_cast h6.2

theorem magnitude_count_toUniform (c : SS.State 6 ℂ) (t : ℝ) :
    (Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (toUniform c x) = t)).card =
      (Finset.univ.filter (fun x : SS.BitString 6 => Complex.normSq (c x) = t)).card := by
  classical
  have he := Equiv.sum_comp (SS.bxorEquiv flip6)
    (fun x : SS.BitString 6 => if Complex.normSq (c x) = t then (1 : ℕ) else 0)
  simpa [toUniform, SixQubit.CodeEquiv.flipAct] using he

/-- Actual original-gauge inputs certify the entire magnitude corollary,
including coefficient multiplicities on the original full cube. -/
theorem magnitudes_fully_certified (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight SixQubit.Orbit9Real.av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c,d] 3) :
    (∃ a b : Fin 6, MagnitudePattern (toUniform c) (toUniform d) a b) ∧
      ElevenCoefficientPattern c d := by
  refine ⟨original_magnitude_pattern c d hc hd hnc hnd hdist, ?_⟩
  have H : FullKL (toUniform c) (toUniform d) := {
    support0 := toUniform_support0 c hc
    support1 := toUniform_support1 d hd
    norm0 := (innerC_toUniform c c).trans hnc
    norm1 := (innerC_toUniform d d).trans hnd
    distance := hasDistance_toUniform c d hdist }
  have hm := eleven_coefficient_pattern (toUniform c) (toUniform d) H
  simpa only [ElevenCoefficientPattern, magnitude_count_toUniform] using hm

end
end SixQubit.Orbit9Universal
