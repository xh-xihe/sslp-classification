import MainTheory.Orbit3ScalarCategoryRealization

/-! # The actual logical-Pauli shift and complementary category masses -/

namespace MainTheory.Orbit3CategoryShift

open MainTheory.PhysicalPauliCategories MainTheory.PauliCategoryFourier
open MainTheory.Orbit3CategoryBridge MainTheory.OrderTwoScalarBridge
open MainTheory.PauliCategoryAverages
open SixQubit.Generated.Orbit3CategoryRows
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def shift (P : SS.PauliString 6) : SS.PauliString 6 := ⟨P.x, SS.bxor P.z orbit3Mask⟩

theorem shift_involution (P : SS.PauliString 6) : shift (shift P) = P := by
  cases P with
  | mk px pz =>
    change SS.PauliString.mk px (SS.bxor (SS.bxor pz orbit3Mask) orbit3Mask) = _
    rw [SS.bxor_assoc, SS.bxor_self, SS.bxor_zero]

def shiftEquiv : SS.PauliString 6 ≃ SS.PauliString 6 where
  toFun := shift
  invFun := shift
  left_inv := shift_involution
  right_inv := shift_involution

def flipLetter (p : Letter) : Letter := letter (x p, !z p)

theorem flipLetter_z : ∀ p : Letter, flipLetter p = 2 ↔ p = 0 := by decide +kernel
theorem flipLetter_x : ∀ p : Letter, x (flipLetter p) = x p := by decide +kernel

theorem zCount_flip (p : Fin 5 → Letter) :
    zCount (fun i => flipLetter (p i)) = identityCount p := by
  unfold zCount identityCount
  simp_rw [flipLetter_z]

theorem transverseCount_flip (p : Fin 5 → Letter) :
    transverseCount (fun i => flipLetter (p i)) = transverseCount p := by
  unfold transverseCount
  simp_rw [flipLetter_x]

theorem word_shift_spectator (P : SS.PauliString 6) : word (shift P) 0 = word P 0 := by
  have hm : orbit3Mask 0 = false := by decide +kernel
  simp only [shift, word, SS.bxor, hm, Bool.xor_false]

theorem word_shift_tail (P : SS.PauliString 6) (i : Fin 5) :
    word (shift P) i.succ = flipLetter (word P i.succ) := by
  have hm : orbit3Mask i.succ = true := by fin_cases i <;> decide +kernel
  have hx := congrArg Prod.fst (letter_bits (P.x i.succ, P.z i.succ))
  have hz := congrArg Prod.snd (letter_bits (P.x i.succ, P.z i.succ))
  dsimp only at hx hz
  unfold flipLetter word shift SS.bxor
  dsimp only
  rw [hx, hz, hm, Bool.xor_true]

theorem category_shift (P : SS.PauliString 6) :
    category (shift P) = errorCategory (complement (categoryIndex P)) := by
  rw [complement_category, categoryIndex_correct]
  unfold category categoryWord
  rw [word_shift_spectator]
  have ht : Fin.tail (word (shift P)) = fun i => flipLetter (Fin.tail (word P) i) := by
    funext i
    exact word_shift_tail P i
  rw [ht, totalDegree_counts, totalDegree_counts, zCount_flip, transverseCount_flip,
    identityCount_eq]

theorem categoryIndex_shift (P : SS.PauliString 6) :
    categoryIndex (shift P) = complement (categoryIndex P) := by
  apply errorCategory_injective
  rw [categoryIndex_correct, category_shift]

theorem category_shift_iff (P : SS.PauliString 6) (e : Fin 42) :
    category (shift P) = errorCategory (complement e) ↔ category P = errorCategory e := by
  rw [category_shift, errorCategory_injective.eq_iff,
    (Function.Involutive.injective complement_involution).eq_iff,
    ← categoryIndex_correct P, errorCategory_injective.eq_iff]

theorem shifted_mass (psi : Fin 2 → SS.State 6 ℂ) (e : Fin 42) :
    (∑ P : SS.PauliString 6,
      if category P = errorCategory e then MainTheory.OrderTwoLabelScalars.a psi (shift P)
      else 0) = mass psi (errorCategory (complement e)) := by
  symm
  calc
    mass psi (errorCategory (complement e)) =
        ∑ P : SS.PauliString 6,
          if category (shift P) = errorCategory (complement e) then
            MainTheory.OrderTwoLabelScalars.a psi (shift P) else 0 := by
      unfold mass
      exact (shiftEquiv.sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P _
      simp only [category_shift_iff]

end
end MainTheory.Orbit3CategoryShift
