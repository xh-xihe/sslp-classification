import Mathlib
import SixQubit.MacWilliams
import SixQubit.ShadowTwisted
import SixQubit.Orbit21Bridge
import SixQubit.Orbit21Bound

/-!
# Orbit 21: the residual sum vanishes

`Orbit21Coef.coef_group_sum` decides the certificate's finite content and
`Orbit21Bridge.cf_group_sum` carries it to Paulis.  What is still needed is the
step from that per-label statement to the vanishing of the residual sum

    sum_F cf F * normSq (trProj psi F),

which is `Averaging.sum_eq_zero_of_average` once the two symmetries are known to
preserve the weights.  That is what this file supplies, and the hypothesis it
takes is exactly the invariance the orbit-specific `melTr_shift` instances
provide.

Keeping the invariance as a hypothesis rather than deriving it here is
deliberate: it is the only place where a code's structure enters, and every
other step above is orbit-independent.
-/

namespace SixQubit.Orbit21Chain

open SS.MacWilliams SixQubit.Orbit21Bridge SixQubit.Averaging

/-- **The residual vanishes.**

Given that the two symmetries preserve the squared projector traces -- which for
a code supported in orbit 21's fibers is what `Orbit21Sym.normSq_trProj_shift`
gives, with the two decided character conditions of `Orbit21Cert` -- the
certificate's residual sum is zero.

The per-label disjunction comes from `cf_group_sum`, whose second branch says
the label is forced; that branch is discharged by `hforced`, the statement that
a forced label really does have vanishing projector trace. -/
theorem residual_vanishes (psi : Fin 2 → SS.State 6 ℂ)
    (hG : ∀ P : SS.PauliString 6,
      Complex.normSq (trProj psi (sigG P)) = Complex.normSq (trProj psi P))
    (hD : ∀ P : SS.PauliString 6,
      Complex.normSq (trProj psi (sigD P)) = Complex.normSq (trProj psi P))
    (hforced : ∀ P : SS.PauliString 6, isForced P →
      Complex.normSq (trProj psi P) = 0) :
    ∑ P : SS.PauliString 6, cf P * Complex.normSq (trProj psi P) = 0 := by
  refine sum_eq_zero_of_average sigG sigD cf
    (fun P => Complex.normSq (trProj psi P)) hG hD (fun P => ?_)
  rcases cf_group_sum P with h | h
  · exact Or.inl h
  · exact Or.inr (hforced P h)

/-- The same conclusion with the two invariance hypotheses merged into the form
a caller will have them: one statement per symmetry, quantified over Paulis. -/
theorem residual_vanishes_of_shift (psi : Fin 2 → SS.State 6 ℂ)
    (hshift : ∀ (σ : SS.PauliString 6 ≃ SS.PauliString 6), σ = sigG ∨ σ = sigD →
      ∀ P, Complex.normSq (trProj psi (σ P)) = Complex.normSq (trProj psi P))
    (hforced : ∀ P : SS.PauliString 6, isForced P →
      Complex.normSq (trProj psi P) = 0) :
    ∑ P : SS.PauliString 6, cf P * Complex.normSq (trProj psi P) = 0 :=
  residual_vanishes psi (hshift sigG (Or.inl rfl)) (hshift sigD (Or.inr rfl)) hforced

end SixQubit.Orbit21Chain
