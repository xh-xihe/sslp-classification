import MainTheory.PaperGeneralSSLP
import MainTheory.GeneralColoredSubspaceConverse

/-! # The arbitrary-subspace converse of `thm:general-sslp-normal-form`

This completes the forward paper-facing theorem in `PaperGeneralSSLP`.
Its inputs are the manuscript's gcd conditions, positive multiplicities,
subspace dimensions, full computational-fiber spans, and basis-independent
KL equations. No basis, orthogonality certificate, or direct-sum assumption
is required from the caller.
-/

namespace MainTheory.PaperGeneralSSLP

open CodeSpec GeneralColoredSubspaces ColoredResidueArithmetic
open ClassificationLevels GlobalClassificationBridge

noncomputable section

variable {n K d q m t : ℕ} [NeZero q] [NeZero m]

/-- The converse paragraph of `thm:general-sslp-normal-form`, with the actual
supplied subspaces and the literal finite diagonal gate retained in the result.
The zero color may be at any designated index; including it in the gcd does
not change the manuscript's gcd of the remaining colors. -/
theorem general_sslp_converse
    (hm : 2 ≤ m) (hmq : m ∣ q) (a : Fin n → ZMod q)
    (hsorted : Monotone fun j => (a j).val)
    (hprimitive : Nat.gcd q (Finset.univ.gcd fun j => (a j).val) = 1)
    (rank : Fin t → ℕ) (hrank : ∀ alpha, 0 < rank alpha)
    (hsum : ∑ alpha, rank alpha = K)
    (base : Fin t) (color : Fin t → ZMod m)
    (hzero : color base = 0) (hdistinct : Function.Injective color)
    (hcolors : Nat.gcd m (Finset.univ.gcd fun alpha => (color alpha).val) = 1)
    (E : Fin t → Submodule ℂ (SS.State n ℂ))
    (hdimension : ∀ alpha, Module.finrank ℂ (E alpha) = rank alpha)
    (hfiber : ∀ alpha, E alpha ≤ Submodule.span ℂ
      ((fun x : SS.BitString n => Pi.single x (1 : ℂ)) ''
        (SS.Sk a (scaledColor q (color alpha)) : Set (SS.BitString n))))
    (hKL : SubspaceCode.HasDistance (⨆ alpha, E alpha) d) :
    iSupIndep E ∧
    Module.finrank ℂ (⨆ alpha, E alpha : Submodule ℂ (SS.State n ℂ)) = K ∧
    ∃ (C : ExactCode n K d) (u : diagonalSymmetryGroup (exactCodeProjector C)),
      codeSpan C.frame = (⨆ alpha, E alpha) ∧
      (u : LocalPhase n) = finiteLocalPhase
        (D3NormalizedFiniteToReal.canonicalRoot q)
        (D3NormalizedFiniteToReal.canonicalRoot_primitive q) a ∧
      orderOf (intrinsicClass (exactCodeProjector C) u) = m ∧
      intrinsicClass (exactCodeProjector C) u ≠ 1 := by
  let S : GeneralColoredSubspaceConverse.ColoredSubspaces n K q m t := {
    modulus_dvd := hmq
    angle := a
    primitive := (primitive_iff_gcd_eq_one a).2 hprimitive
    sorted := hsorted
    rank := rank
    rank_pos := hrank
    rank_sum := hsum
    base := base
    color := color
    color_zero := hzero
    color_distinct := hdistinct
    color_primitive := (primitive_iff_gcd_eq_one color).2 hcolors
    space := E
    dimension := hdimension
    fiber := fun alpha => by
      rw [fiberSubspace_eq_span]
      exact hfiber alpha }
  exact ⟨S.independent, S.finrank_sum, S.sslp_converse hKL hm⟩

end

end MainTheory.PaperGeneralSSLP
