import Mathlib

/-!
# The active face

The maximum-support-rank lemma of `main.tex` (Section 7) rests on one convexity
observation: if for every active variable there is a feasible point positive at
that variable, then averaging those finitely many points gives a *single*
feasible point positive at all of them at once.  Its support is therefore the
full active set, and no feasible point can have larger support.

That observation is what this file proves.  Nothing here is about codes or
moments -- it is a statement about a convex set of nonnegative vectors -- and
separating it out makes clear that the lemma's geometry is elementary and that
the work is entirely in identifying the active set, which the paper does with
exact linear-programming certificates outside Lean.
-/

namespace MainTheory.ActiveFace

variable {iota : Type*} [Fintype iota] [Nonempty iota]

/-- The uniform average of a finite family of points. -/
noncomputable def avg (pt : iota → iota → ℝ) : iota → ℝ :=
  fun j => (∑ k, pt k j) / (Fintype.card iota : ℝ)

/-- **The average is feasible.**  Convexity, with uniform weights. -/
theorem avg_mem (K : Set (iota → ℝ)) (hK : Convex ℝ K)
    (pt : iota → iota → ℝ) (hmem : ∀ k, pt k ∈ K) :
    avg pt ∈ K := by
  have hcard : (0 : ℝ) < (Fintype.card iota : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hw : ∑ _k : iota, ((Fintype.card iota : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have := hK.sum_mem (t := (Finset.univ : Finset iota))
    (fun k _ => le_of_lt (inv_pos.2 hcard)) hw (fun k _ => hmem k)
  have heq : (∑ k, ((Fintype.card iota : ℝ))⁻¹ • pt k) = avg pt := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, avg]
    rw [← Finset.mul_sum, div_eq_inv_mul]
  rwa [heq] at this

/-- **The average is positive wherever any one point is.**

This is the step the lemma needs: the averaged point is simultaneously positive
on every active variable, so its support is the whole active set. -/
theorem avg_pos (pt : iota → iota → ℝ)
    (hnn : ∀ k j, 0 ≤ pt k j) (j : iota) (k0 : iota) (hk0 : 0 < pt k0 j) :
    0 < avg pt j := by
  have hcard : (0 : ℝ) < (Fintype.card iota : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine div_pos ?_ hcard
  have hle : (0 : ℝ) < ∑ k, pt k j := by
    refine Finset.sum_pos' (fun k _ => hnn k j) ⟨k0, Finset.mem_univ k0, hk0⟩
  exact hle

end MainTheory.ActiveFace
