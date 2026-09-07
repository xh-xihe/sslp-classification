import SixQubit.ParityMomentFamily

namespace SixQubit.ParityMomentFamily.Certificate

open scoped BigOperators
open SS.MacWilliams SixQubit.Realize SixQubit.Orbit8Family
open SixQubit.ParityCircleFamily

noncomputable section

set_option maxRecDepth 10000

theorem normSq_trace_model (T : ParityMomentFamily.Certificate) (C S : ℝ)
    (hCS : C^2 + S^2 = 1) (P : SS.PauliString 6) (model : QuadZ)
    (hmodel : CircleZero (QuadZ.sub (ParityCircleFamily.qtrace T.c0 T.c1 T.L0 T.L1 P) model)) :
    Complex.normSq (trProj (T.state C S) P) =
      Complex.normSq (evalQuad C S model) / (T.denominator : ℝ)^4 := by
  have h := eval_zero_of_circle C S hCS _ hmodel
  rw [evalQuad_sub, sub_eq_zero] at h
  rw [trace_eq, h, scale_square]
  simp only [Complex.normSq_mul, map_pow, Complex.normSq_I, one_pow,
    mul_one, Complex.normSq_div, Complex.normSq_one, Complex.normSq_natCast]
  ring

/-- A finite list of nonzero polynomial traces computes the genuine enumerator. -/
theorem Aco_eq_list_model (T : ParityMomentFamily.Certificate) (C S : ℝ)
    (hCS : C^2 + S^2 = 1) (w : ℕ) (L : List (SS.PauliString 6))
    (hnd : L.Nodup) (hweight : ∀ P ∈ L, P.wt = w)
    (model : SS.PauliString 6 → QuadZ)
    (hmodel : ∀ P, P.wt = w → CircleZero
      (QuadZ.sub (ParityCircleFamily.qtrace T.c0 T.c1 T.L0 T.L1 P) (model P)))
    (hzero : ∀ P, P.wt = w → P ∉ L → model P = QuadZ.zero) :
    Aco (T.state C S) w =
      (L.map fun P => Complex.normSq (evalQuad C S (model P))).sum /
        (T.denominator : ℝ)^4 := by
  classical
  let U := Finset.univ.filter fun P : SS.PauliString 6 => P.wt = w
  have hsub : L.toFinset ⊆ U := by
    intro P hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hweight P (List.mem_toFinset.mp hP)⟩
  have hout : ∀ P ∈ U, P ∉ L.toFinset → Complex.normSq (trProj (T.state C S) P) = 0 := by
    intro P hP hn
    have hw : P.wt = w := (Finset.mem_filter.mp hP).2
    rw [normSq_trace_model T C S hCS P (model P) (hmodel P hw),
      hzero P hw (by simpa using hn), evalQuad_zero, Complex.normSq_zero, zero_div]
  rw [Aco]
  change (∑ P ∈ U, Complex.normSq (trProj (T.state C S) P)) = _
  rw [← Finset.sum_subset hsub hout]
  calc
    _ = ∑ P ∈ L.toFinset, Complex.normSq (evalQuad C S (model P)) /
        (T.denominator : ℝ)^4 := by
      apply Finset.sum_congr rfl
      intro P hP
      exact normSq_trace_model T C S hCS P (model P)
        (hmodel P (hweight P (List.mem_toFinset.mp hP)))
    _ = _ := by rw [← Finset.sum_div, List.sum_toFinset _ hnd]

end

end SixQubit.ParityMomentFamily.Certificate
