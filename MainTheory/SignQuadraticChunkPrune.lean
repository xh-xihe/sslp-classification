import MainTheory.RestrictedSignQuadraticMinimum
import MainTheory.SignQuadraticPrune

namespace MainTheory.SignQuadraticChunkPrune

open Matrix MainTheory.SignQuadraticMinimum MainTheory.SignPrefixCertificate
open MainTheory.SignDagCertificate MainTheory.GramSchurCertificate

def fixedHighBits {N : ℕ} (free : ℕ) (mask : Fin (2^N)) : Fin N → Option ℤ :=
  fun j => if j.val < free then none else some (MainTheory.SignRowEnumeration.row mask j)

theorem prefixGood_snoc_of_restricted_minimum {k N : ℕ} {T : ℤ} {B : ℕ}
    (hk : k+1 ≤ N) (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ) (ha : a ≠ 0)
    (hdet : (gram P).det = a) (hAJ : gram P * J = a • 1) (hT : 0 ≤ T)
    (K : Matrix (Fin N) (Fin N) ℤ) (hK : K = P.transpose * J * P)
    (fixed : Fin N → Option ℤ)
    (hbound : ((N : ℤ) * a - restrictedMinimum N 0 0 K fixed) *
      (N : ℤ) ^ (N-(k+1)) < T^2)
    (v : Fin N → ℤ) (hv : ∀ j, v j = 1 ∨ v j = -1) (hf : Matches fixed v) :
    PrefixGood T B hk (Fin.snoc P v) := by
  apply prefixGood_prune hk _ hT
  change (gram (Fin.snoc P v)).det * (N : ℤ) ^ (N-(k+1)) < T^2
  rw [MainTheory.SignQuadraticPrune.gram_snoc_eq_quadratic P v hv J a ha hdet hAJ K hK]
  have hm := restrictedMinimum_le N 0 0 K fixed v hv hf
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (sub_le_sub_left hm _)
    (pow_nonneg (by omega) _)) hbound

theorem prefixGood_of_row_certificates {k N : ℕ} {T : ℤ} {B : ℕ} (hk : k+1 ≤ N)
    (P : Matrix (Fin k) (Fin N) ℤ)
    (h : ∀ mask : Fin (2^N), PrefixGood T B hk (Fin.snoc P (MainTheory.SignRowEnumeration.row mask))) :
    PrefixGood T B (by omega : k ≤ N) P := by
  apply prefixGood_step hk P
  intro v hv
  obtain ⟨mask, rfl⟩ := MainTheory.SignRowEnumeration.row_surjective v hv
  exact h mask

theorem prefixGood_snoc_of_edge {k N L : ℕ} {T : ℤ} {B : ℕ} (hk : k+1 ≤ N)
    (P : Matrix (Fin k) (Fin N) ℤ) (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ)
    (ha : a ≠ 0) (hdet : (gram P).det = a) (hAJ : gram P * J = a • 1)
    (hT : 0 ≤ T) (targets : Fin L → Matrix (Fin (k+1)) (Fin N) ℤ)
    (hTargets : ∀ t, PrefixGood T B hk (targets t)) (mask : Fin (2^N))
    (choice : MainTheory.SignDagFastCertificate.Edge k N L)
    (h : MainTheory.SignDagFastCertificate.EdgeValid T P J a targets mask choice) :
    PrefixGood T B hk (Fin.snoc P (MainTheory.SignRowEnumeration.row mask)) := by
  cases choice with
  | inl w => exact MainTheory.SignDagFastCertificate.PruneData.Valid.prune hk h ha hdet hAJ hT
  | inr tw => exact Transport.Valid.prefixGood hk h (hTargets tw.1)

end MainTheory.SignQuadraticChunkPrune
