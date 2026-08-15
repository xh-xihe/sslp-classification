import SS.ZSeedKL

/-!
# Weight-`≤2` Paulis, parameterized by their support

`KLmatK` quantifies over `∀ P : Fin n → SQ` with `pauliWt P ≤ 2`.  Deciding that
directly makes the kernel enumerate all `4^n` Pauli strings: `16384` at seven
qubits, which is affordable, and `262144` at nine, which is not --- the
`Fintype (Fin n → SQ)` instance builds every one of them as a function value,
and a probe at `n = 9` reached 97 GB of resident memory before it was stopped.

Almost all of that enumeration is discarded by the weight filter.  A Pauli of
weight at most two is the identity outside a set of at most two positions, so it
is determined by that set and by the two letters sitting on it.  This module
makes the parameterization explicit and proves the case distinction, which
replaces the `4^n` enumeration by `n^2 \cdot 16` guarded instances --- `1296` at
nine qubits, of which only the `352` genuine ones reach the expensive check,
because the guards `A ≠ I` and `i < j` are evaluated first.

No `sorry`, no `native_decide`.
-/

namespace DyadicLifts

open SS

variable {n : ℕ}

/-- The Pauli carrying `A` at position `i` and the identity elsewhere. -/
def oneSite (i : Fin n) (A : SQ) : Fin n → SQ := fun k => if k = i then A else SQ.I

/-- The Pauli carrying `A` at `i`, `B` at `j`, and the identity elsewhere.  When
`i = j` the first branch wins, so `twoSite i i A B = oneSite i A`. -/
def twoSite (i j : Fin n) (A B : SQ) : Fin n → SQ :=
  fun k => if k = i then A else if k = j then B else SQ.I

/-- The support of a Pauli string, as a `Finset`; its cardinality is the weight. -/
def pauliSupp (P : Fin n → SQ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => P i ≠ SQ.I)

lemma pauliWt_eq_card (P : Fin n → SQ) : pauliWt P = (pauliSupp P).card := rfl

lemma mem_pauliSupp {P : Fin n → SQ} {i : Fin n} : i ∈ pauliSupp P ↔ P i ≠ SQ.I := by
  simp [pauliSupp]

lemma eq_I_of_not_mem {P : Fin n → SQ} {i : Fin n} (h : i ∉ pauliSupp P) : P i = SQ.I := by
  by_contra hne; exact h (mem_pauliSupp.mpr hne)

/-- **The case distinction.**  A Pauli of weight at most two is the identity, a
one-site Pauli with a non-identity letter, or a two-site Pauli with two
non-identity letters on an ordered pair of positions. -/
theorem pauli_le_two_decomp (P : Fin n → SQ) (h : pauliWt P ≤ 2) :
    (P = fun _ => SQ.I)
    ∨ (∃ (i : Fin n) (A : SQ), A ≠ SQ.I ∧ P = oneSite i A)
    ∨ (∃ (i j : Fin n) (A B : SQ), i < j ∧ A ≠ SQ.I ∧ B ≠ SQ.I ∧ P = twoSite i j A B) := by
  rw [pauliWt_eq_card] at h
  interval_cases hc : (pauliSupp P).card
  · -- weight 0
    left
    have hempty : pauliSupp P = ∅ := Finset.card_eq_zero.mp hc
    funext k
    exact eq_I_of_not_mem (by rw [hempty]; simp)
  · -- weight 1
    right; left
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    have hPi : P i ≠ SQ.I := mem_pauliSupp.mp (by rw [hi]; exact Finset.mem_singleton_self i)
    refine ⟨i, P i, hPi, ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp [oneSite]
    · have : k ∉ pauliSupp P := by rw [hi]; simpa using hk
      simp [oneSite, hk, eq_I_of_not_mem this]
  · -- weight 2
    right; right
    obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hc
    have hPa : P a ≠ SQ.I :=
      mem_pauliSupp.mp (by rw [hs]; exact Finset.mem_insert_self a {b})
    have hPb : P b ≠ SQ.I :=
      mem_pauliSupp.mp (by rw [hs]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
    have hoff : ∀ k, k ≠ a → k ≠ b → P k = SQ.I := by
      intro k hka hkb
      exact eq_I_of_not_mem (by rw [hs]; simp [hka, hkb])
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · refine ⟨a, b, P a, P b, hlt, hPa, hPb, ?_⟩
      funext k
      by_cases hka : k = a
      · subst hka; simp [twoSite]
      · by_cases hkb : k = b
        · subst hkb; simp [twoSite, hka]
        · simp [twoSite, hka, hkb, hoff k hka hkb]
    · refine ⟨b, a, P b, P a, hgt, hPb, hPa, ?_⟩
      funext k
      by_cases hkb : k = b
      · subst hkb; simp [twoSite]
      · by_cases hka : k = a
        · subst hka; simp [twoSite, hkb]
        · simp [twoSite, hkb, hka, hoff k hka hkb]

/-- **The transport, in the form the kernel can afford.**  Three guarded
statements replace the quantifier over all `4^n` Pauli strings. -/
theorem KLmatK_of_sites {S : Finset (BitString n)} {ψ0Z ψ1Z : BitString n → SS.ZSqrt235i}
    (q : ℚ)
    (hI : klAtZ S ψ0Z ψ1Z (fun _ => SQ.I) = true)
    (h1 : ∀ (i : Fin n) (A : SQ), A ≠ SQ.I → klAtZ S ψ0Z ψ1Z (oneSite i A) = true)
    (h2 : ∀ (i j : Fin n) (A B : SQ), i < j → A ≠ SQ.I → B ≠ SQ.I →
            klAtZ S ψ0Z ψ1Z (twoSite i j A B) = true) :
    KLmatK S (fun s => SS.QSqrt235i.smul q (SS.ZSqrt235i.toQ (ψ0Z s)))
            (fun s => SS.QSqrt235i.smul q (SS.ZSqrt235i.toQ (ψ1Z s))) := by
  refine KLmatK_of_int q (fun P hP => ?_)
  rcases pauli_le_two_decomp P hP with hid | ⟨i, A, hA, hEq⟩ | ⟨i, j, A, B, hij, hA, hB, hEq⟩
  · rw [hid]; exact hI
  · rw [hEq]; exact h1 i A hA
  · rw [hEq]; exact h2 i j A B hij hA hB

end DyadicLifts
