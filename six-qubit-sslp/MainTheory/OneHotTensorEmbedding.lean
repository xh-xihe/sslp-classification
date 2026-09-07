import MainTheory.FiniteTensorKernel
import MainTheory.LocalUnitaryKL

/-! # Isometric one-hot encoding of arbitrary finite physical subsystems -/

namespace MainTheory.OneHotTensorEmbedding

open ClassificationLevels

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] {A : S → Type*}
  [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]

set_option linter.unusedSectionVars false

abbrev size (A : S → Type*) [∀ j, Fintype (A j)] := Fintype.card (Sigma A)

def coordinateEquiv : (Sigma A) ≃ Fin (size A) := Fintype.equivFin (Sigma A)

def oneHot (x : ∀ j, A j) : SS.BitString (size A) := fun k =>
  decide (x ((coordinateEquiv (A := A)).symm k).1 = ((coordinateEquiv (A := A)).symm k).2)

@[simp] theorem oneHot_coordinate (x : ∀ j, A j) (j : S) (a : A j) :
    oneHot x (coordinateEquiv (A := A) ⟨j, a⟩) = decide (x j = a) := by
  exact congrArg (fun p : Sigma A => decide (x p.1 = p.2))
    ((coordinateEquiv (A := A)).symm_apply_apply ⟨j, a⟩)

theorem oneHot_injective : Function.Injective (oneHot (A := A)) := by
  intro x y h
  funext j
  have hj := congrFun h (coordinateEquiv (A := A) ⟨j, x j⟩)
  exact (by simpa using hj : y j = x j).symm

def embedding : Matrix (SS.BitString (size A)) (∀ j, A j) ℂ :=
  fun b x => if b = oneHot x then 1 else 0

theorem embedding_gram : (embedding (A := A)).conjTranspose * embedding (A := A) = 1 := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single (oneHot x)]
  · by_cases hxy : x = y
    · subst y
      simp [embedding]
    · have hhot : oneHot x ≠ oneHot y := fun h => hxy (oneHot_injective h)
      simp [embedding, hxy, hhot]
  · intro b _ hb
    simp [embedding, hb]
  · simp

theorem embedding_diagonal (f : SS.BitString (size A) → ℂ) :
    (embedding (A := A)).conjTranspose * Matrix.diagonal f * embedding =
      Matrix.diagonal (fun x => f (oneHot x)) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    embedding, Matrix.diagonal_apply]
  simp only [apply_ite, star_one, star_zero, ite_mul, one_mul, zero_mul,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hxy : x = y
  · subst y
    simp
  · have hhot : oneHot y ≠ oneHot x := fun h => hxy (oneHot_injective h).symm
    simp [hxy, hhot]

def localPhase (u : ∀ j, A j → unitary ℂ) : LocalPhase (size A) := fun k =>
  u ((coordinateEquiv (A := A)).symm k).1 ((coordinateEquiv (A := A)).symm k).2

theorem diagonalValue_oneHot (u : ∀ j, A j → unitary ℂ) (x : ∀ j, A j) :
    diagonalValue (localPhase u) (oneHot x) = ∏ j, (u j (x j) : ℂ) := by
  change (∏ k, (fun p : Sigma A => if decide (x p.1 = p.2) then (u p.1 p.2 : ℂ) else 1)
    ((coordinateEquiv (A := A)).symm k)) = _
  calc
    _ = ∏ p : Sigma A, if decide (x p.1 = p.2) then (u p.1 p.2 : ℂ) else 1 :=
      (coordinateEquiv (A := A)).symm.prod_comp
        (fun p : Sigma A => if decide (x p.1 = p.2) then (u p.1 p.2 : ℂ) else 1)
    _ = _ := ?_
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  simp

theorem diagonalKernel_embedding (u : ∀ j, A j → unitary ℂ) :
    diagonalKernel (localPhase u) * embedding =
      embedding * Matrix.diagonal (fun x => ∏ j, (u j (x j) : ℂ)) := by
  classical
  ext b x
  change (Matrix.diagonal (diagonalValue (localPhase u)) * embedding (A := A)) b x = _
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hb : b = oneHot x
  · subst b
    simp [embedding, diagonalValue_oneHot]
  · simp [embedding, hb]

end

end MainTheory.OneHotTensorEmbedding
