import MainTheory.LocalTensorPermutation

/-!
# Elementary LU equivalence is exactly one tensor product and one permutation

The factors are arbitrary unitary `2 × 2` complex matrices.  This identifies
the repository's equivalence closure with the manuscript's concrete equation.
-/

namespace MainTheory.LocalUnitaryClosure

open ClassificationLevels LocalTensorKernel

noncomputable section

variable {n : ℕ}

def TensorEquivalent (P Q : CodeProjector n) : Prop :=
  ∃ (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (sigma : Equiv.Perm (Fin n)),
    (∀ j, IsOneQubitUnitary (U j)) ∧
    Q.kernel = localPermutationKernel U sigma * P.kernel * star (localPermutationKernel U sigma)

theorem unitary_one : IsOneQubitUnitary (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor <;> simp

theorem unitary_star {U : Matrix (Fin 2) (Fin 2) ℂ} (h : IsOneQubitUnitary U) :
    IsOneQubitUnitary (star U) := by
  simpa only [IsOneQubitUnitary, star_star] using h.symm

theorem unitary_mul {U V : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : IsOneQubitUnitary U) (hV : IsOneQubitUnitary V) : IsOneQubitUnitary (U * V) := by
  constructor
  · calc star (U * V) * (U * V) = star V * (star U * U) * V := by simp [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hU.1]; simpa using hV.1
  · calc (U * V) * star (U * V) = U * (V * star V) * star U := by simp [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hV.2]; simpa using hU.2

theorem tensorEquivalent_refl (P : CodeProjector n) : TensorEquivalent P P := by
  refine ⟨fun _ => 1, 1, fun _ => unitary_one, ?_⟩
  simp [localPermutationKernel]

theorem tensorEquivalent_symm {P Q : CodeProjector n} (h : TensorEquivalent P Q) :
    TensorEquivalent Q P := by
  obtain ⟨U, sigma, hU, hQ⟩ := h
  refine ⟨fun j => star (U (sigma.symm j)), sigma.symm,
    fun j => unitary_star (hU _), ?_⟩
  rw [← localPermutationKernel_star, star_star, hQ]
  have hW := (localPermutationKernel_unitary U hU sigma).1
  calc P.kernel = (star (localPermutationKernel U sigma) * localPermutationKernel U sigma) *
      P.kernel * (star (localPermutationKernel U sigma) * localPermutationKernel U sigma) := by rw [hW]; simp
    _ = _ := by simp [Matrix.mul_assoc]

theorem tensorEquivalent_trans {P Q R : CodeProjector n}
    (hPQ : TensorEquivalent P Q) (hQR : TensorEquivalent Q R) : TensorEquivalent P R := by
  obtain ⟨U, sigma, hU, hQ⟩ := hPQ
  obtain ⟨V, tau, hV, hR⟩ := hQR
  refine ⟨fun j => V j * U (tau j), sigma * tau, fun j => unitary_mul (hV j) (hU _), ?_⟩
  rw [← localPermutationKernel_mul, hR, hQ, star_mul]
  simp [Matrix.mul_assoc]

theorem tensorEquivalent_of_elementary {P Q : CodeProjector n} (h : ElementaryLU P Q) :
    TensorEquivalent P Q := by
  classical
  rcases h with ⟨j, U, hU, hQ⟩ | ⟨sigma, hQ⟩
  · refine ⟨Function.update (fun _ => 1) j U, 1, ?_, ?_⟩
    · intro k
      by_cases hk : k = j
      · subst k; simpa using hU
      · simpa [Function.update_of_ne hk] using unitary_one
    · simpa [localPermutationKernel, tensorKernel_single, conjugateProjector] using hQ
  · exact ⟨fun _ => 1, sigma, fun _ => unitary_one,
      by simpa [localPermutationKernel, conjugateProjector] using hQ⟩

theorem tensorEquivalent_of_luEquivalent {P Q : CodeProjector n} (h : LUEquivalent P Q) :
    TensorEquivalent P Q := by
  induction h with
  | rel P Q h => exact tensorEquivalent_of_elementary h
  | refl P => exact tensorEquivalent_refl P
  | symm _ _ _ ih => exact tensorEquivalent_symm ih
  | trans _ _ _ _ _ ih1 ih2 => exact tensorEquivalent_trans ih1 ih2

/-- A finite tensor product is realized by one elementary step at each site. -/
theorem luEquivalent_of_tensor (P Q : CodeProjector n)
    (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (hU : ∀ j, IsOneQubitUnitary (U j))
    (hQ : Q.kernel = tensorKernel U * P.kernel * star (tensorKernel U)) : LUEquivalent P Q := by
  classical
  have hs (s : Finset (Fin n)) :
      ∀ Q : CodeProjector n,
        Q.kernel = tensorKernel (fun j => if j ∈ s then U j else 1) * P.kernel *
          star (tensorKernel (fun j => if j ∈ s then U j else 1)) → LUEquivalent P Q := by
    induction s using Finset.induction_on with
    | empty =>
        intro Q hQ
        have heq : Q = P := CodeProjector.ext (by simpa using hQ)
        subst Q
        exact Relation.EqvGen.refl P
    | @insert i s hi ih =>
        intro Q hQ
        let V : Fin n → Matrix (Fin 2) (Fin 2) ℂ := fun j => if j ∈ s then U j else 1
        have hV : ∀ j, IsOneQubitUnitary (V j) := by
          intro j
          dsimp [V]
          split_ifs
          · exact hU j
          · exact unitary_one
        let M := conjugated P (tensorKernel V) (tensorKernel_unitary V hV).1
        have hPM : LUEquivalent P M := ih M rfl
        have hstep : tensorKernel (fun j => if j ∈ insert i s then U j else 1)
            = oneQubitKernel i (U i) * tensorKernel V := by
          rw [← tensorKernel_single, ← tensorKernel_mul]
          congr 1
          funext j
          by_cases hji : j = i
          · subst j
            simp [V, hi]
          · simp [V, hji]
        apply Relation.EqvGen.trans _ M _ hPM
        apply luEquivalent_of_oneQubit M Q i (U i) (hU i)
        rw [hQ, hstep]
        simp [M, conjugated, conjugateProjector, star_mul, Matrix.mul_assoc]
  apply hs Finset.univ Q
  simpa using hQ

theorem luEquivalent_of_tensorEquivalent {P Q : CodeProjector n} (h : TensorEquivalent P Q) :
    LUEquivalent P Q := by
  obtain ⟨U, sigma, hU, hQ⟩ := h
  let M := conjugated P (qubitPermutationKernel sigma) (permutationKernel_unitary sigma).1
  have hPM : LUEquivalent P M := luEquivalent_of_permutation P M sigma rfl
  apply Relation.EqvGen.trans _ M _ hPM
  apply luEquivalent_of_tensor M Q U hU
  rw [hQ]
  simp [M, conjugated, localPermutationKernel, star_mul, Matrix.mul_assoc]

/-- **The manuscript's LU equation and the kernel equivalence closure agree.** -/
theorem luEquivalent_iff_tensor (P Q : CodeProjector n) :
    LUEquivalent P Q ↔
      ∃ (U : Fin n → Matrix (Fin 2) (Fin 2) ℂ) (sigma : Equiv.Perm (Fin n)),
        (∀ j, IsOneQubitUnitary (U j)) ∧
        Q.kernel = localPermutationKernel U sigma * P.kernel * star (localPermutationKernel U sigma) :=
  ⟨tensorEquivalent_of_luEquivalent, luEquivalent_of_tensorEquivalent⟩

end

end MainTheory.LocalUnitaryClosure
