import MainTheory.PhysicalPauliCategories
import SixQubit.Generated.Orbit3CategoryFourier
import SixQubit.Generated.Orbit3CategoryRows

/-! # Physical category Fourier coefficients of arbitrary six-qubit Paulis

The finite polynomial expansion is tied to actual tensor Pauli labels. It does
not assume that a submitted scalar array arises from an encoder.
-/

namespace MainTheory.Orbit3CategoryBridge

open MainTheory.PauliCategoryFourier MainTheory.PhysicalPauliCategories
open SS.ShadowTwisted
open scoped BigOperators
open SixQubit.Generated.Orbit3CategoryRows

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

abbrev tailCategories := SixQubit.Generated.Orbit3CategoryFourier.categories
abbrev tailCoefficients := SixQubit.Generated.Orbit3CategoryFourier.coefficients

def tailIndex (p : Fin 5 → Letter) : Fin 21 :=
  ((List.finRange 21).find? (fun i => tailCategories i =
    (zCount p, transverseCount p))).getD 0

theorem tailIndex_correct : ∀ p : Fin 5 → Letter,
    tailCategories (tailIndex p) = (zCount p, transverseCount p) := by
  decide +kernel

theorem identityCount_eq : ∀ p : Fin 5 → Letter,
    identityCount p = 5 - zCount p - transverseCount p := by decide +kernel

theorem tail_pairing_sum (p : Fin 5 → Letter) (e : Fin 21) :
    (∑ q : Fin 5 → Letter,
      if totalDegree q = tailCategories e then totalSign q p else 0) =
        tailCoefficients (tailIndex p) e := by
  rw [category_pairing_sum, factor_product, identityCount_eq]
  have hz : zCount p = (tailCategories (tailIndex p)).1 :=
    (congrArg Prod.fst (tailIndex_correct p)).symm
  have ht : transverseCount p = (tailCategories (tailIndex p)).2 :=
    (congrArg Prod.snd (tailIndex_correct p)).symm
  rw [hz, ht, SixQubit.Generated.Orbit3CategoryFourier.expansion]
  exact SixQubit.Generated.Orbit3CategoryFourier.expanded_coefficient _ _

theorem physical_pairing_sum (P : SS.PauliString 6) (a : Fin 2) (e : Fin 21) :
    (∑ E : SS.PauliString 6,
      if category E = (a.val, tailCategories e) then pairSign E P else 0) =
      (spectatorFactor (word P 0) a.val : ℝ) *
        (tailCoefficients (tailIndex (Fin.tail (word P))) e : ℝ) := by
  rw [physical_category_pairing_sum]
  have h := tail_pairing_sum (Fin.tail (word P)) e
  rw [category_pairing_sum] at h
  simp only [Fin.tail] at h
  rw [h]

def spectatorIndex (P : SS.PauliString 6) : Fin 2 := if word P 0 = 0 then 0 else 1

def categoryIndex (P : SS.PauliString 6) : Fin 42 :=
  ⟨21 * (spectatorIndex P).val + (tailIndex (Fin.tail (word P))).val, by
    have hs := (spectatorIndex P).isLt
    have ht := (tailIndex (Fin.tail (word P))).isLt
    omega⟩

theorem categoryIndex_tail (P : SS.PauliString 6) :
    errorTail (categoryIndex P) = tailIndex (Fin.tail (word P)) := by
  apply Fin.ext
  dsimp only [errorTail, categoryIndex]
  have hs := (spectatorIndex P).isLt
  have ht := (tailIndex (Fin.tail (word P))).isLt
  omega

theorem categoryIndex_spectator (P : SS.PauliString 6) :
    errorSpectator (categoryIndex P) = spectatorIndex P := by
  apply Fin.ext
  dsimp only [errorSpectator, categoryIndex]
  have hs := (spectatorIndex P).isLt
  have ht := (tailIndex (Fin.tail (word P))).isLt
  omega

theorem categoryIndex_correct (P : SS.PauliString 6) :
    errorCategory (categoryIndex P) = category P := by
  unfold errorCategory
  rw [categoryIndex_spectator, categoryIndex_tail]
  change ((spectatorIndex P).val, tailCategories (tailIndex (Fin.tail (word P)))) = category P
  rw [tailIndex_correct]
  unfold category categoryWord
  rw [totalDegree_counts]
  congr 1
  unfold spectatorIndex spectator
  split_ifs <;> rfl

theorem category_column_iff (P : SS.PauliString 6) (c : Fin 24) :
    category P = SixQubit.Generated.Orbit3Scalar.categories c ↔
      categoryIndex P = columnCode c := by
  rw [← categoryIndex_correct, ← (column_category c).1]
  exact errorCategory_injective.eq_iff

end
end MainTheory.Orbit3CategoryBridge
