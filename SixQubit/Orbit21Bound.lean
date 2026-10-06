import Mathlib
import SixQubit.MacWilliams
import SixQubit.ShadowTwisted
import SixQubit.Averaging
import SixQubit.Pin

/-!
# From a Farkas certificate to a lower bound

Orbit 21's argument bounds `A_2` from below by writing `A_2 - 1` as a positive
combination of quantities that are individually nonnegative.  The combination is
specific to that orbit, but the step from it to the bound is not, and this file
carries the general form.

The certificate is an identity

    (A_2 - 1) - sum_j lam_j * (nonneg_j) = sum_F c_F * normSq (trProj psi F),

whose right side vanishes because the coefficient does, label by label, after
averaging over the code's symmetries.  Each `nonneg_j` is one of

  * `a_E`, a squared modulus;
  * `b_E = frob psi E / K`, a sum of squared moduli, via `frob_of_KL` equal to
    `a_E` for every Pauli of weight at most two;
  * `s_E`, nonnegative by `ShadowTwisted.altT_sum_nonneg`.

so the whole subtracted sum is nonnegative and `A_2 >= 1` follows.  In the
unnormalized convention of `MacWilliams.Aco`, where `Aco_0 = 4`, that reads
`Aco_2 >= 4`, which is exactly what `Pin.pin_low_of_bound` consumes.
-/

namespace SixQubit.Orbit21Bound

open SS.MacWilliams SS.ShadowTwisted SixQubit.Averaging

variable {n K : ℕ}

/-! ## The two nonnegative quantities the certificate uses -/

/-- `frob` is a sum of squared moduli. -/
lemma frob_nonneg (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    0 ≤ frob psi P :=
  Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))

/-- The complete shadow coefficient of a label, up to the positive factor the
transform carries.  Nonnegative for every label, by the twisted identity. -/
lemma shadow_nonneg (psi : Fin K → SS.State n ℂ) (E : SS.PauliString n) :
    0 ≤ ∑ P : SS.PauliString n,
        ((-1 : ℝ)) ^ P.wt * pairSign E P * Complex.normSq (trProj psi P) :=
  altT_sum_nonneg psi E

/-! ## The certificate, in the abstract -/

/-- **A Farkas certificate gives a bound.**

`lhs` is the quantity to be bounded, `sub` the nonnegative combination
subtracted from it, and `res` the residual sum over labels.  If the residual
vanishes and the subtracted part is nonnegative, the bound follows.  Stated this
plainly it is arithmetic, but it is the shape every certificate in this
development ends in, and keeping it separate is what lets the orbit-specific
work be exactly the two hypotheses. -/
theorem bound_of_certificate {lhs sub res : ℝ}
    (hcert : lhs - sub = res) (hsub : 0 ≤ sub) (hres : res = 0) : 0 ≤ lhs := by
  rw [hres] at hcert
  linarith

/-- The residual vanishes when its coefficient does after averaging.

This is `Averaging.sum_eq_zero_of_average` at the Pauli labels, with the weights
being the squared projector traces: those are invariant under the symmetries of
a code, which is what the orbit-specific `melTr_shift` instances supply. -/
theorem residual_eq_zero (psi : Fin K → SS.State n ℂ)
    (σ τ : SS.PauliString n ≃ SS.PauliString n) (c : SS.PauliString n → ℝ)
    (hσ : ∀ P, Complex.normSq (trProj psi (σ P)) = Complex.normSq (trProj psi P))
    (hτ : ∀ P, Complex.normSq (trProj psi (τ P)) = Complex.normSq (trProj psi P))
    (hzero : ∀ P, c P + c (σ P) + c (τ P) + c (σ (τ P)) = 0
              ∨ Complex.normSq (trProj psi P) = 0) :
    ∑ P : SS.PauliString n, c P * Complex.normSq (trProj psi P) = 0 :=
  sum_eq_zero_of_average σ τ c (fun P => Complex.normSq (trProj psi P))
    hσ hτ hzero

/-! ## The six-qubit consequence -/

/-- **The bound, in the form the squeeze consumes.**

`Aco_2 >= 4` is `A_2 >= 1` in the unnormalized convention, and
`Pin.pin_low_of_bound` turns it into the whole enumerator. -/
theorem enumerator_of_A2_bound (psi : Fin 2 → SS.State 6 ℂ)
    (hd3 : SS.HasDistance psi 3) (hA0 : Aco psi 0 = 4)
    (hlow : 4 ≤ Aco psi 2) :
    Aco psi 1 = 0 ∧ Aco psi 2 = 4 ∧ Aco psi 3 = 0
      ∧ Aco psi 4 = 44 ∧ Aco psi 5 = 64 ∧ Aco psi 6 = 12 := by
  obtain ⟨h4, h5, h6⟩ := macwilliams_six psi hd3 hA0
  obtain ⟨hj, hoth⟩ :=
    SixQubit.Pin.pin_low_of_bound psi hd3 hA0 2 (Or.inr (Or.inl rfl)) hlow
  have e1 := hoth 1 (Or.inl rfl) (by norm_num)
  have e3 := hoth 3 (Or.inr (Or.inr rfl)) (by norm_num)
  exact ⟨e1, hj, e3, by linarith, by linarith, by linarith⟩

end SixQubit.Orbit21Bound
