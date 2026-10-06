import MainTheory.SignDagCertificate

/-! Shared integer intermediates for the pruning checker.  The two vectors
are proposed data and both defining identities are checked in the kernel. -/

namespace MainTheory.SignDagFastCertificate

open Matrix SignMatrixCertificate SignPrefixCertificate SignDagCertificate GramSchurCertificate
open scoped BigOperators

structure PruneData (k : ℕ) where
  crossVector : Fin k → ℤ
  productVector : Fin k → ℤ

def PruneData.Valid {k N : ℕ} (T : ℤ) (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ) (mask : Fin (2^N)) (w : PruneData k) : Prop :=
  (∀ i, cross P (SignRowEnumeration.row mask) i = w.crossVector i) ∧
  (∀ i, ∑ j, J i j * w.crossVector j = w.productVector i) ∧
  ((N : ℤ)*a - ∑ i, w.crossVector i * w.productVector i) * (N : ℤ)^(N-(k+1)) < T^2

instance {k N : ℕ} (T : ℤ) (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ) (mask : Fin (2^N)) (w : PruneData k) :
    Decidable (w.Valid T P J a mask) := by unfold PruneData.Valid; infer_instance

theorem PruneData.Valid.prune {k N : ℕ} {T : ℤ} {B : ℕ} (hk : k+1 ≤ N)
    {P : Matrix (Fin k) (Fin N) ℤ} {J : Matrix (Fin k) (Fin k) ℤ} {a : ℤ}
    {mask : Fin (2^N)} {w : PruneData k} (h : w.Valid T P J a mask)
    (ha : a ≠ 0) (hdet : (gram P).det = a) (hAJ : gram P * J = a • 1)
    (hT : 0 ≤ T) : PrefixGood T B hk (Fin.snoc P (SignRowEnumeration.row mask)) := by
  rcases h with ⟨hc, hp, hbound⟩
  apply prefixGood_prune hk _ hT
  change (gram (Fin.snoc P (SignRowEnumeration.row mask))).det * _ < _
  rw [det_gram_snoc P _ (SignRowEnumeration.row_isSign mask) J a ha hdet hAJ]
  simp_rw [hc, mul_assoc, ← Finset.mul_sum, hp]
  exact hbound

abbrev Edge (k N L : ℕ) := PruneData k ⊕ (Fin L × Transport (k+1) N)

def EdgeValid {k N L : ℕ} (T : ℤ) (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ)
    (targets : Fin L → Matrix (Fin (k+1)) (Fin N) ℤ)
    (mask : Fin (2^N)) (choice : Edge k N L) : Prop :=
  match choice with
  | .inl w => w.Valid T P J a mask
  | .inr (t, w) => w.Valid (Fin.snoc P (SignRowEnumeration.row mask)) (targets t)

instance {k N L : ℕ} (T : ℤ) (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ)
    (targets : Fin L → Matrix (Fin (k+1)) (Fin N) ℤ)
    (mask : Fin (2^N)) (choice : Edge k N L) :
    Decidable (EdgeValid T P J a targets mask choice) := by
  cases choice with
  | inl w => unfold EdgeValid; infer_instance
  | inr x => rcases x with ⟨t, w⟩; unfold EdgeValid; infer_instance

theorem prefixGood_node {k N L : ℕ} {T : ℤ} {B : ℕ} (hk : k+1 ≤ N)
    (P : Matrix (Fin k) (Fin N) ℤ) (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ)
    (ha : a ≠ 0) (hdet : (gram P).det = a) (hAJ : gram P * J = a • 1)
    (hT : 0 ≤ T) (targets : Fin L → Matrix (Fin (k+1)) (Fin N) ℤ)
    (hTargets : ∀ t, PrefixGood T B hk (targets t))
    (choices : Fin (2^N) → Edge k N L)
    (hEdges : ∀ mask, EdgeValid T P J a targets mask (choices mask)) :
    PrefixGood T B (by omega : k ≤ N) P := by
  apply prefixGood_step hk P
  intro v hv
  obtain ⟨mask, rfl⟩ := SignRowEnumeration.row_surjective v hv
  have h := hEdges mask
  cases he : choices mask with
  | inl w =>
    rw [he] at h
    exact PruneData.Valid.prune hk h ha hdet hAJ hT
  | inr x =>
    rcases x with ⟨t, w⟩
    rw [he] at h
    exact Transport.Valid.prefixGood hk h (hTargets t)

end MainTheory.SignDagFastCertificate
