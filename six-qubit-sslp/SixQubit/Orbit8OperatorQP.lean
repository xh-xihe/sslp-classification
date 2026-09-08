import SixQubit.Orbit8UniversalLadderClose

/-!
# `eq:o8QP`: the operator form

`Orbit8UniversalLadderClose.Q_eigen` proves that `Q` acts as `r = 1/6` on each
of the two logical words, which is what the manuscript's proof of
`eq:o8QP` establishes.  The manuscript states the conclusion as an operator
identity, `Q P = r P`.  This file records that step: `Q` and the code
projector are linear, so the two eigenvalue equations are the operator
identity applied to an arbitrary vector.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators
open SixQubit

noncomputable section

lemma lower_smul (ud : Fin 6 → ℂ) (z : ℂ) (f : SS.BitString 6 → ℂ) :
    lower ud (fun x => z * f x) = fun x => z * lower ud f x := by
  funext x
  unfold lower
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : x i = false
  · simp [h]
    ring
  · simp [h]

lemma raise_add (ud : Fin 6 → ℂ) (f g : SS.BitString 6 → ℂ) :
    raise ud (fun x => f x + g x) = fun x => raise ud f x + raise ud g x := by
  funext x
  unfold raise
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : x i = true
  · simp [h]
    ring
  · simp [h]

lemma lower_add (ud : Fin 6 → ℂ) (f g : SS.BitString 6 → ℂ) :
    lower ud (fun x => f x + g x) = fun x => lower ud f x + lower ud g x := by
  funext x
  unfold lower
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : x i = false
  · simp [h]
    ring
  · simp [h]

lemma Qact_smul (ud : Fin 6 → ℂ) (z : ℂ) (f : SS.BitString 6 → ℂ) :
    Qact ud (fun x => z * f x) = fun x => z * Qact ud f x := by
  unfold Qact
  rw [lower_smul, raise_smul]

lemma Qact_add (ud : Fin 6 → ℂ) (f g : SS.BitString 6 → ℂ) :
    Qact ud (fun x => f x + g x) = fun x => Qact ud f x + Qact ud g x := by
  unfold Qact
  rw [lower_add, raise_add]

/-- The code projector of the logical pair: `P = |0_L><0_L| + |1_L><1_L|`. -/
def codeProj (c d f : SS.BitString 6 → ℂ) : SS.BitString 6 → ℂ :=
  fun x => SS.innerC c f * c x + SS.innerC d f * d x

/-- **`eq:o8QP`.**  `Q P = r P`, with `r = 1/6`.

The manuscript derives this from the two ladder identities; `Q_eigen` is that
derivation, and linearity of `Q` turns the two eigenvalue equations into the
operator identity. -/
theorem QP_eq (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c, d] 3) (f : SS.BitString 6 → ℂ) :
    Qact (u d) (codeProj c d f) = fun x => (1 / 6 : ℂ) * codeProj c d f x := by
  obtain ⟨h0, h1⟩ := Q_eigen c d hc hd hnc hnd hcode
  have hsplit : Qact (u d) (codeProj c d f)
      = fun x => Qact (u d) (fun y => SS.innerC c f * c y) x
          + Qact (u d) (fun y => SS.innerC d f * d y) x := by
    rw [← Qact_add]
    rfl
  rw [hsplit, Qact_smul, Qact_smul, h0, h1]
  funext x
  simp only [codeProj]
  ring

end

end SixQubit.Orbit8Universal
