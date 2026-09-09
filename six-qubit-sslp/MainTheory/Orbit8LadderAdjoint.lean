import MainTheory.Orbit8LadderMatrices

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.Orbit8LadderAdjoint

open MainTheory.Orbit8LadderMatrices SixQubit.Orbit8Universal

theorem minus_adjoint (i : Fin 6) : minus i=(plus i).conjTranspose := by
  ext x y
  simp [minus,minusData,plus,Matrix.conjTranspose_apply]

set_option maxHeartbeats 0 in
theorem minus_data_action : ∀ (i : Fin 6) (x y : SS.BitString 6),
    minusData i x y=if x i=false ∧ y=SS.bxor x (SS.stdBasis i) then 1 else 0 := by decide +kernel

theorem minus_action (i : Fin 6) (f : SS.State 6 ℂ) (x : SS.BitString 6) :
    (minus i).mulVec f x=if x i=false then f (SS.bxor x (SS.stdBasis i)) else 0 := by
  cases hx : x i <;> simp [minus,minus_data_action,Matrix.mulVec,dotProduct,hx]

theorem lowering_action (ud : Fin 6 → ℂ) (f : SS.State 6 ℂ) :
    lower ud f=fun x => ∑ i,star (ud i)*(minus i).mulVec f x := by
  simp only [minus_action]
  funext x
  unfold lower
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem product_action (i j : Fin 6) (f : SS.State 6 ℂ) :
    (plus i*minus j).mulVec f=rl i j f := by
  rw [← Matrix.mulVec_mulVec]
  funext x
  rw [plus_action,minus_action]
  rfl

end MainTheory.Orbit8LadderAdjoint
