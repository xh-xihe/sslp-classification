import MainTheory.SignDagCertificate

namespace MainTheory.SignPrefixBetaBound

open Matrix BinaryBeta SignBinaryBridge SignMatrixCertificate SignPrefixCertificate

theorem signLift_first_row {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (j : Fin (n+1)) : signLift C 0 j = 1 := by
  have he : borderEquiv n (Sum.inl 0) = (0 : Fin (n+1)) := rfl
  have hi : (borderEquiv n).symm (0 : Fin (n+1)) = Sum.inl 0 := by
    rw [← he, Equiv.symm_apply_apply]
  change signLiftBlock C ((borderEquiv n).symm 0) ((borderEquiv n).symm j) = 1
  rw [hi]
  generalize (borderEquiv n).symm j = a
  rcases a with a | a
  · fin_cases a
    rfl
  · rfl

theorem betaBound_of_allOnesPrefix {n B : ℕ}
    (h : PrefixGood ((2 : ℤ)^n * (B+1)) B (by omega : 1 ≤ n+1)
      (fun _ _ => 1)) : BetaBound n B := by
  apply SignMatrixCertificate.betaBound_of_good
  intro C hC
  apply h (signLift C) (signLift_isSign C hC)
  intro i j
  fin_cases i
  exact signLift_first_row C j

end MainTheory.SignPrefixBetaBound
