import MainTheory.CodeSpec
import SixQubit.CodeBridge

/-!
# Binary moments of normalized sector projectors

For arbitrary code dimension and distance, every binary monomial of degree
below the distance has the same expectation in every positive-rank sector.
The sector probability is the diagonal of the full orthogonal projector
divided by its rank; sectors need not be one dimensional.
-/

namespace MainTheory.GeneralSectorMoments

open scoped BigOperators
open SS.MacWilliams
open MainTheory.CodeSpec

noncomputable section

variable {n K t : ℕ}

/-- The binary monomial supported on `J`, including the empty monomial. -/
def binaryMonomial (J : Finset (Fin n)) (x : SS.BitString n) : ℝ :=
  ∏ j ∈ J, if x j then 1 else 0

private theorem binaryMonomial_eq_ite (J : Finset (Fin n)) (x : SS.BitString n) :
    binaryMonomial J x = if ∀ j ∈ J, x j = true then 1 else 0 := by
  classical
  by_cases h : ∀ j ∈ J, x j = true
  · rw [if_pos h]
    exact Finset.prod_eq_one fun j hj => by simp [h j hj]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j, hj, hx⟩ := h
    apply Finset.prod_eq_zero hj
    simp [Bool.eq_false_of_not_eq_true hx]

private theorem monomial_fourier (J : Finset (Fin n)) (x : SS.BitString n) :
    (2 : ℝ) ^ J.card * binaryMonomial J x =
      ∑ z ∈ cube J, chi z (SS.ones n) * chi z x := by
  classical
  simp_rw [← chi_bxor_right]
  rw [sum_chi_cube, binaryMonomial_eq_ite]
  have h : (∀ i ∈ J, SS.bxor (SS.ones n) x i = false) ↔
      ∀ i ∈ J, x i = true := by
    simp [SS.bxor_apply, SS.ones]
  simp only [h]
  split_ifs <;> simp

/-- A single logical vector's binary moment. -/
def wordMoment (psi : Fin K → SS.State n ℂ) (k : Fin K)
    (J : Finset (Fin n)) : ℝ :=
  ∑ x, Complex.normSq (psi k x) * binaryMonomial J x

private theorem charOn_eq_chi (c : SS.State n ℂ) (z : SS.BitString n) :
    SixQubit.charOn Finset.univ c z = ∑ x, Complex.normSq (c x) * chi z x := by
  simp only [SixQubit.charOn]
  apply Finset.sum_congr rfl
  intro x _
  have h := congrArg Complex.re (signC_bdot z x (Complex.normSq (c x) : ℂ))
  cases hb : SS.bdot z x <;> simpa [hb, SS.signC, mul_comm] using h

private theorem pureZ_weight_le {J : Finset (Fin n)} {z : SS.BitString n}
    (hz : z ∈ cube J) : (⟨fun _ => false, z⟩ : SS.PauliString n).wt ≤ J.card := by
  apply Finset.card_le_card
  intro i hi
  have hi' : z i = true := by simpa [SS.PauliString.wt] using hi
  by_contra h
  have := mem_cube.mp hz i h
  simp [this] at hi'

private theorem word_character_eq (psi : Fin K → SS.State n ℂ) {d : ℕ}
    (hd : SS.HasDistance psi d) {J : Finset (Fin n)} (hJ : J.card < d)
    {z : SS.BitString n} (hz : z ∈ cube J) (k l : Fin K) :
    (∑ x, Complex.normSq (psi k x) * chi z x) =
      ∑ x, Complex.normSq (psi l x) * chi z x := by
  have hw := pureZ_weight_le hz
  obtain ⟨c, hc⟩ := hd (⟨fun _ => false, z⟩ : SS.PauliString n) (by omega)
  have hk := hc k k
  have hl := hc l l
  simp only [ite_true] at hk hl
  rw [SixQubit.innerC_pureZ_eq_charOn Finset.univ (psi k) (by simp)] at hk
  rw [SixQubit.innerC_pureZ_eq_charOn Finset.univ (psi l) (by simp)] at hl
  have hh := Complex.ofReal_injective (hk.trans hl.symm)
  simpa only [charOn_eq_chi] using hh

/-- Every logical vector has the same binary moments below the code distance. -/
theorem wordMoment_eq (psi : Fin K → SS.State n ℂ) {d : ℕ}
    (hd : SS.HasDistance psi d) {J : Finset (Fin n)} (hJ : J.card < d)
    (k l : Fin K) : wordMoment psi k J = wordMoment psi l J := by
  have expansion : ∀ k, (2 : ℝ) ^ J.card * wordMoment psi k J =
      ∑ z ∈ cube J, chi z (SS.ones n) *
        (∑ x, Complex.normSq (psi k x) * chi z x) := by
    intro k
    simp only [wordMoment, Finset.mul_sum]
    calc
      _ = ∑ x, Complex.normSq (psi k x) *
          ((2 : ℝ) ^ J.card * binaryMonomial J x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        simp_rw [monomial_fourier, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro x _
        ring
  apply mul_left_cancel₀ (pow_ne_zero J.card (by norm_num : (2 : ℝ) ≠ 0))
  rw [expansion, expansion]
  exact Finset.sum_congr rfl fun z hz => by rw [word_character_eq psi hd hJ hz k l]

/-- A sector's orthonormal frame, extracted by an actual reindexing of the code. -/
def sectorFrame (F : OrthonormalFrame n K) (rank : Fin t → ℕ)
    (e : Fin K ≃ (α : Fin t) × Fin (rank α)) (α : Fin t) :
    OrthonormalFrame n (rank α) where
  vec r := F.vec (e.symm ⟨α, r⟩)
  orthonormal r s := by simpa using F.orthonormal (e.symm ⟨α, r⟩) (e.symm ⟨α, s⟩)

/-- The full sector-projector diagonal divided by its rank. -/
def sectorProbability (F : OrthonormalFrame n K) (rank : Fin t → ℕ)
    (e : Fin K ≃ (α : Fin t) × Fin (rank α)) (α : Fin t) (x : SS.BitString n) : ℝ :=
  (∑ r : Fin (rank α), Complex.normSq (F.vec (e.symm ⟨α, r⟩) x)) / rank α

/-- The probability is exactly the normalized diagonal of the orthogonal projector. -/
theorem sectorProbability_eq_projector (F : OrthonormalFrame n K) (rank : Fin t → ℕ)
    (e : Fin K ≃ (α : Fin t) × Fin (rank α)) (α : Fin t) (x : SS.BitString n) :
    (sectorProbability F rank e α x : ℂ) =
      projectorKernel (sectorFrame F rank e α) x x / (rank α : ℂ) := by
  simp only [sectorProbability, projectorKernel, sectorFrame, Complex.ofReal_div,
    Complex.ofReal_sum, Complex.ofReal_natCast]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [Complex.normSq_eq_conj_mul_self]
  simp [mul_comm]

theorem sectorProbability_nonneg (F : OrthonormalFrame n K) (rank : Fin t → ℕ)
    (e : Fin K ≃ (α : Fin t) × Fin (rank α)) (α : Fin t) (x : SS.BitString n) :
    0 ≤ sectorProbability F rank e α x :=
  div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem sectorProbability_sum_eq_one (F : OrthonormalFrame n K) (rank : Fin t → ℕ)
    (hpos : ∀ α, 0 < rank α) (e : Fin K ≃ (α : Fin t) × Fin (rank α)) (α : Fin t) :
    ∑ x, sectorProbability F rank e α x = 1 := by
  have hmass : ∀ r : Fin (rank α),
      ∑ x : SS.BitString n, Complex.normSq (F.vec (e.symm ⟨α, r⟩) x) = 1 := by
    intro r
    have h := SixQubit.massOn_eq_one Finset.univ (F.vec (e.symm ⟨α, r⟩))
      (by simp) (by simpa using F.orthonormal (e.symm ⟨α, r⟩) (e.symm ⟨α, r⟩))
    simpa [SixQubit.massOn] using h
  simp only [sectorProbability, ← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [hmass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact div_self (by exact_mod_cast (hpos α).ne')

theorem sectorProbability_eq_zero_of_support (F : OrthonormalFrame n K) (rank : Fin t → ℕ)
    (e : Fin K ≃ (α : Fin t) × Fin (rank α)) (S : Fin t → Set (SS.BitString n))
    (hs : ∀ α r x, x ∉ S α → F.vec (e.symm ⟨α, r⟩) x = 0)
    (α : Fin t) (x : SS.BitString n) (hx : x ∉ S α) :
    sectorProbability F rank e α x = 0 := by
  simp [sectorProbability, fun r => hs α r x hx]

/-- All positive-rank sectors have equal moments for every `|J| < d`. -/
theorem sector_moment_eq (F : OrthonormalFrame n K) (rank : Fin t → ℕ)
    (hpos : ∀ α, 0 < rank α) (e : Fin K ≃ (α : Fin t) × Fin (rank α))
    {d : ℕ} (hd : SS.HasDistance F.vec d) {J : Finset (Fin n)} (hJ : J.card < d)
    (α β : Fin t) :
    (∑ x, sectorProbability F rank e α x * binaryMonomial J x) =
      ∑ x, sectorProbability F rank e β x * binaryMonomial J x := by
  let k := e.symm ⟨α, ⟨0, hpos α⟩⟩
  have hsector : ∀ γ, (∑ x, sectorProbability F rank e γ x * binaryMonomial J x) =
      wordMoment F.vec k J := by
    intro γ
    calc
      _ = (∑ r : Fin (rank γ), wordMoment F.vec (e.symm ⟨γ, r⟩) J) / rank γ := by
        simp only [sectorProbability, div_mul_eq_mul_div, ← Finset.sum_div,
          Finset.sum_mul, wordMoment]
        rw [Finset.sum_comm]
      _ = (∑ _r : Fin (rank γ), wordMoment F.vec k J) / rank γ := by
        congr 1
        exact Finset.sum_congr rfl fun r _ => wordMoment_eq F.vec hd hJ _ k
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_div_cancel_left₀ _ (by exact_mod_cast (hpos γ).ne')
  rw [hsector, hsector]

end

end MainTheory.GeneralSectorMoments
