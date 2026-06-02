import DyadicLifts.SSResidue

/-!
# The general carry–tag lift framework (`dyadic_lifts.tex`, Section 2)

This module formalizes the *general* carry–tag criterion of the main paper
`dyadic_lifts.tex`, Section 2 — the part that is independent of the concrete Bell
lift:

* `CarryDephasedKL`  — `Definition (Carry-dephased KL condition)`.
* `TagInvisible`     — `Definition (Tag invisibility)`.
* `tagLift`          — the lifted logical state `|i↑⟩ = Σₚ ψ_{i,p} ⊗ τ_p`.
* `strong_carry_tag` — `Proposition (Strong carry-tag lift criterion)`: if the seed
  carry decomposition is carry-dephased KL up to weight `e` and the tag pair is
  invisible to order `e`, then the lifted code satisfies the KL equations for every
  Pauli `A ⊗ B` of total weight `≤ e`.

**Scope note.** This is a faithful formalization of a paper result that the dyadic
Bell lift deliberately does *not* satisfy at `d = 3` (the weight-`2` operator `ZZ`
reads the Bell parity, so the Bell tag is not invisible to order `2`).  Accordingly
this module is standalone and is **not** imported by the two-anchor ladder; it
records the general sufficient criterion for completeness of the paper's Section 2.

The general *phase*-lift template (`thm:phase-lift-template`) is the eigenvalue
calculation `Udiag_smul_of_suppIn` from `SSResidue`; it is re-exported below as
`phase_lift_template`.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

variable {n t : ℕ}

/-! ## Finite-sum linearity of the matrix element -/

lemma mel_sum_left {ι : Type*} (P : Fin n → SQ) (ψ₁ : Hil n) (s : Finset ι) (f : ι → Hil n) :
    mel (∑ i ∈ s, f i) P ψ₁ = ∑ i ∈ s, mel (f i) P ψ₁ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, mel_add_left, ih]

lemma mel_sum_right {ι : Type*} (ψ₀ : Hil n) (P : Fin n → SQ) (s : Finset ι) (f : ι → Hil n) :
    mel ψ₀ P (∑ i ∈ s, f i) = ∑ i ∈ s, mel ψ₀ P (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, mel_add_right, ih]

/-! ## The general carry–tag framework -/

/-- **Definition (Carry-dephased KL condition).**
A two-piece carry decomposition `ψ i p` (logical label `i`, carry bit `p`) is
*carry-dephased KL up to weight `e`* if for every old-block Pauli `A` of weight `≤ e`
the carry-summed matrix element `Σₚ ⟨ψ_{i,p}|A|ψ_{j,p}⟩` equals `λ_A δ_{ij}`. -/
def CarryDephasedKL (e : ℕ) (ψ : Bool → Bool → Hil n) : Prop :=
  ∀ A : Fin n → SQ, pauliWt A ≤ e →
    ∃ lam : ℂ, ∀ i j : Bool, (∑ p : Bool, mel (ψ i p) A (ψ j p)) = if i = j then lam else 0

/-- **Definition (Tag invisibility).**
A tag pair `τ` is *invisible to order `e`* if for every tag Pauli `B` of weight `≤ e`
the tag matrix element `⟨τ_p|B|τ_q⟩` equals `μ_B δ_{pq}`. -/
def TagInvisible (e : ℕ) (τ : Bool → Hil t) : Prop :=
  ∀ B : Fin t → SQ, pauliWt B ≤ e →
    ∃ mu : ℂ, ∀ p q : Bool, mel (τ p) B (τ q) = if p = q then mu else 0

/-- The lifted logical state `|i↑⟩ = Σₚ ψ_{i,p} ⊗ τ_p`. -/
noncomputable def tagLift (ψ : Bool → Bool → Hil n) (τ : Bool → Hil t) (i : Bool) :
    Hil (n + t) := ∑ p : Bool, (ψ i p) ⊗ᵥ (τ p)

/-- Core factorization: under tag invisibility (witness `mu`), the lifted matrix
element factors as `μ_B · Σₚ ⟨ψ_{i,p}|A|ψ_{j,p}⟩`. -/
lemma tagLift_mel_factor (ψ : Bool → Bool → Hil n) (τ : Bool → Hil t)
    (A : Fin n → SQ) (B : Fin t → SQ) (mu : ℂ)
    (hmu : ∀ p q : Bool, mel (τ p) B (τ q) = if p = q then mu else 0) (i j : Bool) :
    mel (tagLift ψ τ i) (Fin.append A B) (tagLift ψ τ j)
      = mu * ∑ p : Bool, mel (ψ i p) A (ψ j p) := by
  unfold tagLift
  rw [mel_sum_left, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [mel_sum_right]
  have hterm : ∀ q : Bool, mel (ψ i p ⊗ᵥ τ p) (Fin.append A B) (ψ j q ⊗ᵥ τ q)
      = if p = q then mu * mel (ψ i p) A (ψ j q) else 0 := by
    intro q
    rw [mel_append, hmu p q]
    by_cases hpq : p = q
    · simp only [if_pos hpq]; ring
    · simp only [if_neg hpq]; ring
  rw [Finset.sum_congr rfl (fun q _ => hterm q),
    Finset.sum_ite_eq Finset.univ p (fun q => mu * mel (ψ i p) A (ψ j q)),
    if_pos (Finset.mem_univ p)]

/-- **Proposition (Strong carry-tag lift criterion).**
If the seed carry decomposition is carry-dephased KL up to weight `e` and the tag
pair is invisible to order `e`, then the lifted code satisfies the KL equations for
every Pauli `A ⊗ B` of total weight `≤ e`: the off-diagonal matrix elements vanish
and the diagonal matrix elements are independent of the logical label. -/
theorem strong_carry_tag {e : ℕ} {ψ : Bool → Bool → Hil n} {τ : Bool → Hil t}
    (hkl : CarryDephasedKL e ψ) (htag : TagInvisible e τ)
    (A : Fin n → SQ) (B : Fin t → SQ) (hwt : pauliWt (Fin.append A B) ≤ e) :
    (∀ i j : Bool, i ≠ j →
        mel (tagLift ψ τ i) (Fin.append A B) (tagLift ψ τ j) = 0) ∧
      (∀ i j : Bool,
        mel (tagLift ψ τ i) (Fin.append A B) (tagLift ψ τ i)
          = mel (tagLift ψ τ j) (Fin.append A B) (tagLift ψ τ j)) := by
  rw [pauliWt_append] at hwt
  obtain ⟨mu, hmu⟩ := htag B (by omega)
  obtain ⟨lam, hlam⟩ := hkl A (by omega)
  refine ⟨fun i j hij => ?_, fun i j => ?_⟩
  · rw [tagLift_mel_factor ψ τ A B mu hmu i j, hlam i j, if_neg hij, mul_zero]
  · rw [tagLift_mel_factor ψ τ A B mu hmu i i, tagLift_mel_factor ψ τ A B mu hmu j j,
      hlam i i, hlam j j, if_pos rfl, if_pos rfl]

/-- **General phase-lift template** (`thm:phase-lift-template`): a state supported in a
refined residue block `b (mod m')` is an eigenvector of the transversal diagonal
`U_{m'}` with eigenvalue `ζ_{m'}^b`.  This is exactly `Udiag_smul_of_suppIn`,
re-exported here under the paper's framework name. -/
alias phase_lift_template := Udiag_smul_of_suppIn

end DyadicLifts
