-- Generated semantic endpoint for the fully kernel-checked beta-six bound.
import MainTheory.Generated.BinaryBetaSixKernel.Cover.K0.Shard000
import MainTheory.BinaryBetaSixCanonical
import MainTheory.BinaryBetaSixLower

namespace MainTheory.Generated.BinaryBetaSixKernel.Certificate

open MainTheory.BinaryBeta
open MainTheory.BinaryBetaSixCanonical
open MainTheory.OuterCompleteness
open MainTheory.OuterEnumeration

/-- Every in-range weakly increasing six-tuple is dispatched by Lean's
six-level `Fin 8` coverage tree. -/
theorem allCanonical : AllCanonicalBottomBound 9 := by
  intro p hp
  rcases hp with ⟨hrange, hmono⟩
  let a0 : Fin 8 := ⟨p 0, hrange 0⟩
  let a1 : Fin 8 := ⟨p 1, hrange 1⟩
  let a2 : Fin 8 := ⟨p 2, hrange 2⟩
  let a3 : Fin 8 := ⟨p 3, hrange 3⟩
  let a4 : Fin 8 := ⟨p 4, hrange 4⟩
  let a5 : Fin 8 := ⟨p 5, hrange 5⟩
  have h01 : a0.val <= a1.val := by
    simpa [a0, a1] using
      hmono (show (0 : Fin 6) <= 1 by decide)
  have h12 : a1.val <= a2.val := by
    simpa [a1, a2] using
      hmono (show (1 : Fin 6) <= 2 by decide)
  have h23 : a2.val <= a3.val := by
    simpa [a2, a3] using
      hmono (show (2 : Fin 6) <= 3 by decide)
  have h34 : a3.val <= a4.val := by
    simpa [a3, a4] using
      hmono (show (3 : Fin 6) <= 4 by decide)
  have h45 : a4.val <= a5.val := by
    simpa [a4, a5] using
      hmono (show (4 : Fin 6) <= 5 by decide)
  have hbound := MainTheory.Generated.BinaryBetaSixKernel.Cover.K0.Shard000.cover_root a0 a1 a2 a3 a4 a5 h01 h12 h23 h34 h45
  have hvec : p = angle6 a0.val a1.val a2.val a3.val a4.val a5.val := by
    funext i
    fin_cases i <;> rfl
  rw [hvec]
  exact hbound

theorem upper : BetaBound 6 9 :=
  betaSixBound_of_allCanonicalBottomBound allCanonical

theorem betaExact : BetaExact 6 9 :=
  ⟨upper, MainTheory.BinaryBetaSixLower.betaSixAttained⟩

end MainTheory.Generated.BinaryBetaSixKernel.Certificate
