import Mathlib
import SS.Pauli

/-! The half-angle coordinate flip on the actual modular residue fibers,
for arbitrary modulus and number of physical coordinates. -/
set_option autoImplicit false
namespace MainTheory.HalfAngleFiberFlip
open scoped BigOperators
variable {n q : ℕ}

theorem half_modulus (k : ℕ) : (k : ZMod (2*k))+(k : ZMod (2*k))=0 := by
  have h : ((2*k : ℕ) : ZMod (2*k))=0 := by simp
  push_cast at h
  linear_combination h

theorem negative_half (δ : ZMod q) (hδ : δ+δ=0) : -δ=δ := by
  linear_combination -hδ

theorem weight_shift (a : Fin n → ZMod q) (i : Fin n) (δ : ZMod q)
    (hai : a i=δ) (hδ : δ+δ=0) (x : SS.BitString n) :
    SS.weight a (SS.bxor x (SS.stdBasis i))=SS.weight a x+δ := by
  rw [← SS.flipBit_eq_bxor_stdBasis,SS.weight_flipBit,hai]
  cases x i
  · simp only [Bool.false_eq_true,if_false]
  · simp only [if_true]
    rw [negative_half δ hδ]

theorem flip_involutive (i : Fin n) :
    Function.Involutive (fun x : SS.BitString n => SS.bxor x (SS.stdBasis i)) := by
  intro x
  change SS.bxor (SS.bxor x (SS.stdBasis i)) (SS.stdBasis i)=x
  rw [← SS.flipBit_eq_bxor_stdBasis,← SS.flipBit_eq_bxor_stdBasis,SS.flipBit_flipBit]

theorem zero_to_half (a : Fin n → ZMod q) (i : Fin n) (δ : ZMod q)
    (hai : a i=δ) (hδ : δ+δ=0) (x : SS.BitString n) :
    SS.weight a (SS.bxor x (SS.stdBasis i))=δ ↔ SS.weight a x=0 := by
  rw [weight_shift a i δ hai hδ]
  constructor
  · intro h
    exact add_right_cancel (show SS.weight a x+δ=0+δ by simpa only [zero_add] using h)
  · intro h
    rw [h,zero_add]

theorem fiber_bijection (a : Fin n → ZMod q) (i : Fin n) (δ : ZMod q)
    (hai : a i=δ) (hδ : δ+δ=0) :
    (Finset.univ.filter (fun x : SS.BitString n => SS.weight a x=δ))=
      (Finset.univ.filter (fun x : SS.BitString n => SS.weight a x=0)).image
        (fun x => SS.bxor x (SS.stdBasis i)) := by
  classical
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · intro hx
    refine ⟨SS.bxor x (SS.stdBasis i),?_,flip_involutive i x⟩
    rw [weight_shift a i δ hai hδ,hx,hδ]
  · rintro ⟨y,hy,rfl⟩
    exact (zero_to_half a i δ hai hδ y).2 hy

end MainTheory.HalfAngleFiberFlip
