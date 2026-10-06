import Mathlib

/-! # Unitary matrix subgroups of bounded exponent are finite

The proof uses a finite alphabet of possible traces and a finite spanning
family of group matrices. No finite-generation hypothesis on the group is
needed.
-/

namespace MainTheory.BoundedUnitaryGroup

noncomputable section

open scoped Matrix ComplexOrder

private def sumAlphabet (S : Set ℂ) : ℕ → Set ℂ
  | 0 => {0}
  | k + 1 => {0} ∪ (fun p : ℂ × ℂ => p.1 + p.2) '' (S ×ˢ sumAlphabet S k)

private theorem finite_sumAlphabet (S : Set ℂ) (hS : S.Finite) (k : ℕ) :
    (sumAlphabet S k).Finite := by
  induction k with
  | zero => exact Set.finite_singleton _
  | succ k ih => exact (Set.finite_singleton _).union ((hS.prod ih).image _)

private theorem zero_mem_sumAlphabet (S : Set ℂ) (k : ℕ) : 0 ∈ sumAlphabet S k := by
  cases k <;> simp [sumAlphabet]

private theorem sum_mem_sumAlphabet (S : Set ℂ) (s : Multiset ℂ) (k : ℕ)
    (hs : ∀ a ∈ s, a ∈ S) (hk : s.card ≤ k) : s.sum ∈ sumAlphabet S k := by
  induction s using Multiset.induction_on generalizing k with
  | empty => simpa using zero_mem_sumAlphabet S k
  | @cons a s ih =>
    cases k with
    | zero => simp only [Multiset.card_cons] at hk; omega
    | succ k =>
      have ha : a ∈ S := hs a (Multiset.mem_cons_self _ _)
      have ht : s.sum ∈ sumAlphabet S k := ih k
        (fun b hb => hs b (Multiset.mem_cons_of_mem hb)) (by simpa using hk)
      exact Set.mem_union_right _ ⟨(a, s.sum), ⟨ha, ht⟩, by simp⟩

private theorem finite_power_roots (N : ℕ) (hN : 0 < N) :
    {z : ℂ | z ^ N = 1}.Finite := by
  simpa [Polynomial.IsRoot, sub_eq_zero] using
    (Polynomial.finite_setOf_isRoot
      (Polynomial.X_pow_sub_C_ne_zero hN (1 : ℂ)))

variable {L : Type*} [Fintype L] [DecidableEq L]

private theorem trace_mem_alphabet (A : Matrix L L ℂ) (N : ℕ) (hA : A ^ N = 1) :
    Matrix.trace A ∈ sumAlphabet {z : ℂ | z ^ N = 1} (Fintype.card L) := by
  classical
  cases isEmpty_or_nonempty L with
  | inl h =>
    letI := h
    simpa [Matrix.trace] using zero_mem_sumAlphabet {z : ℂ | z ^ N = 1} (Fintype.card L)
  | inr h =>
    letI := h
    rw [Matrix.trace_eq_sum_roots_charpoly]
    apply sum_mem_sumAlphabet
    · intro z hz
      have hr : A.charpoly.IsRoot z := (Polynomial.mem_roots A.charpoly_monic.ne_zero).mp hz
      have hp := spectrum.pow_mem_pow A N (Matrix.mem_spectrum_of_isRoot_charpoly hr)
      simpa [hA, spectrum.one_eq] using hp
    · simpa only [Matrix.charpoly_natDegree_eq_dim] using Polynomial.card_roots' A.charpoly

/-- Bounded exponent alone restricts all matrix traces to a finite set. -/
theorem finite_trace_values (N : ℕ) (hN : 0 < N) :
    {z : ℂ | ∃ A : Matrix L L ℂ, A ^ N = 1 ∧ Matrix.trace A = z}.Finite := by
  apply (finite_sumAlphabet _ (finite_power_roots N hN) (Fintype.card L)).subset
  rintro z ⟨A, hA, rfl⟩
  exact trace_mem_alphabet A N hA

/-- A unitary matrix subgroup with one positive common exponent is finite.
The group is not assumed to be finitely generated or closed. -/
theorem finite_of_exponent (G : Subgroup (Matrix.unitaryGroup L ℂ))
    (N : ℕ) (hN : 0 < N) (hexp : ∀ g : G, g ^ N = 1) : Finite G := by
  classical
  let ρ : G → Matrix L L ℂ := fun g => g.val.val
  have hmul (g h : G) : ρ (g * h) = ρ g * ρ h := rfl
  have hinv (g : G) : ρ (g⁻¹) = (ρ g).conjTranspose := rfl
  have hp (g : G) : (ρ g) ^ N = 1 := by
    simpa only [ρ, Subgroup.coe_pow, SubmonoidClass.coe_pow,
      Subgroup.coe_one, Submonoid.coe_one] using
      congrArg (fun g : G => ρ g) (hexp g)
  let S : Set (Matrix L L ℂ) := Set.range ρ
  have hfg : (Submodule.span ℂ S).FG :=
    (Submodule.fg_iff_finiteDimensional _).mpr inferInstance
  obtain ⟨b, hb, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp hfg
  let Z : Set ℂ := {z | ∃ A : Matrix L L ℂ, A ^ N = 1 ∧ Matrix.trace A = z}
  have hZ : Z.Finite := finite_trace_values N hN
  letI := hZ.fintype
  let f : G → (b → Z) := fun g x => ⟨Matrix.trace (ρ g * x.val), by
    obtain ⟨h, hh⟩ := hb x.property
    refine ⟨ρ (g * h), hp (g * h), ?_⟩
    rw [hmul, hh]⟩
  apply Finite.of_injective f
  intro g h hgh
  let Δ := ρ g - ρ h
  let D : Submodule ℂ (Matrix L L ℂ) := {
    carrier := {A | Matrix.trace (Δ * A) = 0}
    zero_mem' := by simp
    add_mem' := by
      intro A B hA hB
      change Matrix.trace (Δ * A) = 0 at hA
      change Matrix.trace (Δ * B) = 0 at hB
      change Matrix.trace (Δ * (A + B)) = 0
      simp only [Matrix.mul_add, Matrix.trace_add, hA, hB, add_zero]
    smul_mem' := by
      intro c A hA
      change Matrix.trace (Δ * A) = 0 at hA
      change Matrix.trace (Δ * (c • A)) = 0
      simp only [Matrix.mul_smul, Matrix.trace_smul, hA, smul_zero] }
  have hbD : Submodule.span ℂ (b : Set (Matrix L L ℂ)) ≤ D := by
    apply Submodule.span_le.mpr
    intro A hA
    change Matrix.trace ((ρ g - ρ h) * A) = 0
    have he := congrArg Subtype.val (congrFun hgh ⟨A, hA⟩)
    change Matrix.trace (ρ g * A) = Matrix.trace (ρ h * A) at he
    simpa only [Matrix.sub_mul, Matrix.trace_sub, sub_eq_zero] using he
  have hΔ : Δ.conjTranspose ∈ Submodule.span ℂ S := by
    change (ρ g - ρ h).conjTranspose ∈ _
    rw [Matrix.conjTranspose_sub, ← hinv, ← hinv]
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨g⁻¹, rfl⟩)
      (Submodule.subset_span ⟨h⁻¹, rfl⟩)
  rw [hspan] at hΔ
  have hzero : Matrix.trace (Δ * Δ.conjTranspose) = 0 := hbD hΔ
  have he : ρ g = ρ h := sub_eq_zero.mp
    (Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hzero)
  exact Subtype.ext (Subtype.ext he)

/-- A uniform upper bound on element orders also suffices; factorial B is a
positive common exponent, including the vacuous B=0 case. -/
theorem finite_of_bounded_order (G : Subgroup (Matrix.unitaryGroup L ℂ))
    (B : ℕ) (hB : ∀ g : G, ∃ m : ℕ, 0 < m ∧ m ≤ B ∧ g ^ m = 1) : Finite G := by
  apply finite_of_exponent G B.factorial (Nat.factorial_pos B)
  intro g
  obtain ⟨m, hm, hmB, hpow⟩ := hB g
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hm hmB
  rw [hk, pow_mul, hpow, one_pow]

end

end MainTheory.BoundedUnitaryGroup
