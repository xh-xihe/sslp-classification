import MainTheory.SignPrefixCertificate
import MainTheory.SignRowEnumeration
import MainTheory.GramSchurCertificate

/-! A finite edge checker, independent of the external graph search. -/

namespace MainTheory.SignDagCertificate

open Matrix SignMatrixCertificate SignPrefixCertificate GramSchurCertificate
open scoped BigOperators

structure Transport (k N : ℕ) where
  rows : Fin k → Fin k
  columns : Fin N → Fin N
  rowSigns : Fin k → ℤ
  columnSigns : Fin N → ℤ

def Transport.Valid {k N : ℕ} (w : Transport k N)
    (P Q : Matrix (Fin k) (Fin N) ℤ) : Prop :=
  Function.Bijective w.rows ∧ Function.Bijective w.columns ∧
  (∀ i, w.rowSigns i = 1 ∨ w.rowSigns i = -1) ∧
  (∀ j, w.columnSigns j = 1 ∨ w.columnSigns j = -1) ∧
  ∀ i j, P i j = w.rowSigns i * Q (w.rows i) (w.columns j) * w.columnSigns j

instance {k N : ℕ} (w : Transport k N) (P Q : Matrix (Fin k) (Fin N) ℤ) :
    Decidable (w.Valid P Q) := by unfold Transport.Valid; infer_instance

theorem Transport.Valid.prefixGood {k N : ℕ} {T : ℤ} {B : ℕ} (hk : k ≤ N)
    {w : Transport k N} {P Q : Matrix (Fin k) (Fin N) ℤ}
    (hw : w.Valid P Q) (hQ : PrefixGood T B hk Q) : PrefixGood T B hk P := by
  rcases hw with ⟨hr, hc, hu, hv, he⟩
  exact prefixGood_signed hk hQ (Equiv.ofBijective w.rows hr)
    (Equiv.ofBijective w.columns hc) w.rowSigns w.columnSigns hu hv he

def nextDet {k N : ℕ} (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ) (mask : Fin (2^N)) : ℤ :=
  (N : ℤ)*a - ∑ i, ∑ j,
    cross P (SignRowEnumeration.row mask) i * J i j * cross P (SignRowEnumeration.row mask) j

def EdgeValid {k N L : ℕ} (T : ℤ) (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ)
    (targets : Fin L → Matrix (Fin (k+1)) (Fin N) ℤ)
    (mask : Fin (2^N)) (choice : Option (Fin L × Transport (k+1) N)) : Prop :=
  match choice with
  | none => nextDet P J a mask * (N : ℤ)^(N-(k+1)) < T^2
  | some (t, w) => w.Valid (Fin.snoc P (SignRowEnumeration.row mask)) (targets t)

instance {k N L : ℕ} (T : ℤ) (P : Matrix (Fin k) (Fin N) ℤ)
    (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ)
    (targets : Fin L → Matrix (Fin (k+1)) (Fin N) ℤ)
    (mask : Fin (2^N)) (choice : Option (Fin L × Transport (k+1) N)) :
    Decidable (EdgeValid T P J a targets mask choice) := by
  cases choice with
  | none => unfold EdgeValid; infer_instance
  | some x => rcases x with ⟨t, w⟩; unfold EdgeValid; infer_instance

theorem prefixGood_node {k N L : ℕ} {T : ℤ} {B : ℕ} (hk : k+1 ≤ N)
    (P : Matrix (Fin k) (Fin N) ℤ) (J : Matrix (Fin k) (Fin k) ℤ) (a : ℤ)
    (ha : a ≠ 0) (hdet : (gram P).det = a) (hAJ : gram P * J = a • 1)
    (hT : 0 ≤ T) (targets : Fin L → Matrix (Fin (k+1)) (Fin N) ℤ)
    (hTargets : ∀ t, PrefixGood T B hk (targets t))
    (choices : Fin (2^N) → Option (Fin L × Transport (k+1) N))
    (hEdges : ∀ mask, EdgeValid T P J a targets mask (choices mask)) :
    PrefixGood T B (by omega : k ≤ N) P := by
  apply prefixGood_step hk P
  intro v hv
  obtain ⟨mask, rfl⟩ := SignRowEnumeration.row_surjective v hv
  have h := hEdges mask
  cases he : choices mask with
  | none =>
    rw [he] at h
    apply prefixGood_prune hk _ hT
    change (gram (Fin.snoc P (SignRowEnumeration.row mask))).det * _ < _
    rw [det_gram_snoc P _ (SignRowEnumeration.row_isSign mask) J a ha hdet hAJ]
    exact h
  | some x =>
    rcases x with ⟨t, w⟩
    rw [he] at h
    exact Transport.Valid.prefixGood hk h (hTargets t)

theorem forall_chunks {c d : ℕ} (P : Fin (d*c) → Prop)
    (h : ∀ b : Fin d, ∀ i : Fin c, P (finProdFinEquiv (b, i))) : ∀ x, P x := by
  intro x
  simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using
    h (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2

end MainTheory.SignDagCertificate
