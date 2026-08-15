import DyadicLifts.PauliCoord

/-!
# Hermiticity of bare Pauli strings, and the Pauli split

Two fully proved facts the KL propagation needs:

* `mel_conj_symm` — bare Pauli strings are self-adjoint:
  `conj (mel x A y) = mel y A x` (so a diagonal matrix element is real).
* `pauliSplit` / `pauliWt_split` — every `P : Fin (n+2) → SQ` factors as the tensor
  `Fin.append (Pl P) (Pr P)` of its old-block and new-block restrictions, with
  additive weight.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

variable {n : ℕ}

/-! ## Hermiticity -/

/-- Each single-qubit Pauli matrix element is Hermitian. -/
lemma sqME_conj (P : SQ) (a b : Bool) : conj (sqME P a b) = sqME P b a := by
  cases P <;> cases a <;> cases b <;> simp [sqME, Complex.conj_I]

/-- The bare-Pauli matrix element is Hermitian: `conj ⟨s|P|t⟩ = ⟨t|P|s⟩`. -/
lemma pauliME_conj (P : Fin n → SQ) (s t : BitString n) :
    conj (pauliME P s t) = pauliME P t s := by
  unfold pauliME
  rw [map_prod]
  refine Finset.prod_congr rfl ?_
  intro i _
  exact sqME_conj (P i) (s i) (t i)

/-- **Self-adjointness of the Pauli action:** `⟪papply A y, x⟫ = ⟪y, papply A x⟫`. -/
lemma papply_adjoint (A : Fin n → SQ) (x y : Hil n) :
    ⟪papply A y, x⟫ = ⟪y, papply A x⟫ := by
  unfold inn papply
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
  rw [pauliME_conj A s t]
  ring

/-- **Self-adjointness of `mel`:** `conj (mel x A y) = mel y A x`. -/
lemma mel_conj_symm (x y : Hil n) (A : Fin n → SQ) :
    conj (mel x A y) = mel y A x := by
  rw [mel, inn_conj, mel]
  exact papply_adjoint A x y

/-- A diagonal matrix element is real (equal to its own conjugate). -/
lemma mel_self_real (x : Hil n) (A : Fin n → SQ) :
    conj (mel x A x) = mel x A x := mel_conj_symm x x A

/-! ## The Pauli split `Fin (n+2) → SQ ≃ tensor` -/

/-- Old-block restriction of a Pauli on `n+2` qubits. -/
def Pl (P : Fin (n + 2) → SQ) : Fin n → SQ := fun i => P (Fin.castAdd 2 i)

/-- New-block restriction of a Pauli on `n+2` qubits. -/
def Pr (P : Fin (n + 2) → SQ) : Fin 2 → SQ := fun i => P (Fin.natAdd n i)

@[simp] lemma Pl_append (A : Fin n → SQ) (B : Fin 2 → SQ) : Pl (Fin.append A B) = A := by
  funext i; simp [Pl, Fin.append_left]

@[simp] lemma Pr_append (A : Fin n → SQ) (B : Fin 2 → SQ) : Pr (Fin.append A B) = B := by
  funext i; simp [Pr, Fin.append_right]

/-- Every Pauli on `n+2` qubits is the tensor of its two restrictions. -/
lemma pauliSplit (P : Fin (n + 2) → SQ) : Fin.append (Pl P) (Pr P) = P := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]; rfl
  · rw [Fin.append_right]; rfl

/-- The weight splits across the Pauli split. -/
lemma pauliWt_split (P : Fin (n + 2) → SQ) :
    pauliWt P = pauliWt (Pl P) + pauliWt (Pr P) := by
  conv_lhs => rw [← pauliSplit P]
  rw [pauliWt_append]

/-- If a Pauli string has weight zero, every tensor factor is the identity. -/
lemma pauliWt_eq_zero_iff (P : Fin n → SQ) :
    pauliWt P = 0 ↔ P = fun _ => SQ.I := by
  constructor
  · intro h
    funext i
    by_contra hPi
    have hi : i ∈ Finset.univ.filter (fun j => P j ≠ SQ.I) := by
      simp [hPi]
    have hpos : 0 < pauliWt P := by
      rw [pauliWt]
      exact Finset.card_pos.mpr ⟨i, hi⟩
    omega
  · intro h
    subst h
    rw [pauliWt]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    simp

end DyadicLifts
