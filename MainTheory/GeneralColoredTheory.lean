import MainTheory.GeneralColoredSubspaces
import MainTheory.GeneralSectorMoments

/-! # General colored SSLP probabilities and all moments below target distance -/

namespace MainTheory.GeneralColoredTheory

open GeneralColoredConverse GeneralColoredSubspaces ColoredResidueArithmetic

noncomputable section

variable {n K d q m t : ℕ} [NeZero q] [NeZero m]
  (S : GeneralColoredConverse.ColoredFrame n K q m t)

/-- The probability associated to the whole sector projector, including degeneracy. -/
def probability (alpha : Fin t) (x : SS.BitString n) : ℝ :=
  GeneralSectorMoments.sectorProbability S.frame S.rank S.reindex alpha x

theorem probability_eq_projector (alpha : Fin t) (x : SS.BitString n) :
    (probability S alpha x : ℂ) =
      CodeSpec.projectorKernel (ColoredFrame.sectorFrame S alpha) x x / (S.rank alpha : ℂ) :=
  GeneralSectorMoments.sectorProbability_eq_projector S.frame S.rank S.reindex alpha x

theorem probability_nonneg (alpha : Fin t) (x : SS.BitString n) :
    0 ≤ probability S alpha x :=
  GeneralSectorMoments.sectorProbability_nonneg S.frame S.rank S.reindex alpha x

theorem probability_sum_eq_one (alpha : Fin t) : ∑ x, probability S alpha x = 1 :=
  GeneralSectorMoments.sectorProbability_sum_eq_one S.frame S.rank S.rank_pos S.reindex alpha

theorem probability_eq_zero_outside_fiber (alpha : Fin t) (x : SS.BitString n)
    (hx : x ∉ SS.Sk S.angle (scaledColor q (S.color alpha))) :
    probability S alpha x = 0 := by
  apply GeneralSectorMoments.sectorProbability_eq_zero_of_support S.frame S.rank S.reindex
    (fun beta => (SS.Sk S.angle (scaledColor q (S.color beta)) : Set (SS.BitString n))) ?_ alpha x hx
  intro beta r y hy
  by_contra h
  have hf := S.fiber (S.reindex.symm ⟨beta, r⟩) y h
  apply hy
  simpa only [Equiv.apply_symm_apply] using hf

/-- **`eq:general-sector-moments`**, for every binary degree below the actual
target distance, on precisely the sectors of the colored normal form. -/
theorem all_binary_moments_eq (hd : SS.HasDistance S.frame.vec d)
    (J : Finset (Fin n)) (hJ : J.card < d) (alpha beta : Fin t) :
    (∑ x, probability S alpha x * ∏ j ∈ J, (if x j then (1 : ℝ) else 0)) =
      ∑ x, probability S beta x * ∏ j ∈ J, (if x j then (1 : ℝ) else 0) :=
  GeneralSectorMoments.sector_moment_eq S.frame S.rank S.rank_pos S.reindex hd hJ alpha beta

/-- The colors, multiplicities, and full-fiber subspaces of the manuscript. -/
theorem colored_subspace_data :
    Nat.gcd q (Finset.univ.gcd fun j => (S.angle j).val) = 1 ∧
    Nat.gcd m (Finset.univ.gcd fun alpha => (S.color alpha).val) = 1 ∧
    (∑ alpha, S.rank alpha) = K ∧
    (∀ alpha, Module.finrank ℂ (ColoredFrame.sectorSpace S alpha) = S.rank alpha) ∧
    (∀ alpha, ColoredFrame.sectorSpace S alpha ≤ Submodule.span ℂ
      ((fun x : SS.BitString n => Pi.single x (1 : ℂ)) ''
        (SS.Sk S.angle (scaledColor q (S.color alpha)) : Set (SS.BitString n)))) ∧
    (⨆ alpha, ColoredFrame.sectorSpace S alpha) = CodeSpec.codeSpan S.frame :=
  ⟨(primitive_iff_gcd_eq_one S.angle).1 S.primitive, S.colors_gcd, S.sum_rank,
    ColoredFrame.sectorSpace_finrank S, ColoredFrame.sectorSpace_le_computational_span S,
    ColoredFrame.iSup_sectorSpace S⟩

end

end MainTheory.GeneralColoredTheory
