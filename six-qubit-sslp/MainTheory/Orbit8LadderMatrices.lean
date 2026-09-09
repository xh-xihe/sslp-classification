import MainTheory.Orbit8SpinSemantics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace MainTheory.Orbit8LadderMatrices

open SixQubit.Orbit8Universal MainTheory.Orbit8SpinSemantics
open MainTheory.LocalTensorKernel MainTheory.PauliTransferTwo

def plusData (i : Fin 6) (x y : SS.BitString 6) : ℤ :=
  if x i=true ∧ y=SS.bxor x (SS.stdBasis i) then 1 else 0
def minusData (i : Fin 6) (x y : SS.BitString 6) : ℤ := plusData i y x
def spinData (x y : SS.BitString 6) : ℤ := if y=SS.complement x then spinSign x else 0

noncomputable def plus (i : Fin 6) : Matrix (SS.BitString 6) (SS.BitString 6) ℂ :=
  fun x y => (plusData i x y : ℂ)
noncomputable def minus (i : Fin 6) : Matrix (SS.BitString 6) (SS.BitString 6) ℂ :=
  fun x y => (minusData i x y : ℂ)
noncomputable def spin : Matrix (SS.BitString 6) (SS.BitString 6) ℂ :=
  fun x y => (spinData x y : ℂ)

theorem local_ketbra_entries : ∀ (i : Fin 6) (x y : SS.BitString 6),
    plusData i x y=if x i=true ∧ y i=false ∧ (∀ j,j ≠ i → x j=y j) then 1 else 0 := by decide

theorem transpose_data : ∀ (i : Fin 6) (x y : SS.BitString 6),
    (if y i then spinData (SS.bxor y (SS.stdBasis i)) x else 0)=
      spinSign x*minusData i (SS.complement x) y ∧
    spinSign x*minusData i (SS.complement x) y=
      -(if x i then spinData (SS.bxor x (SS.stdBasis i)) y else 0) := by decide +kernel

theorem plus_action (i : Fin 6) (f : SS.State 6 ℂ) (x : SS.BitString 6) :
    (plus i).mulVec f x=if x i then f (SS.bxor x (SS.stdBasis i)) else 0 := by
  cases hx : x i <;> simp [plus,plusData,Matrix.mulVec,dotProduct,hx]

theorem raising_action (ud : Fin 6 → ℂ) (f : SS.State 6 ℂ) :
    raise ud f=fun x => ∑ i,ud i*(plus i).mulVec f x := by
  simp only [plus_action]
  funext x
  unfold raise
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem plus_spin_entry (i : Fin 6) (x y : SS.BitString 6) :
    (plus i*spin) x y=if x i then (spinData (SS.bxor x (SS.stdBasis i)) y : ℂ) else 0 := by
  cases hx : x i <;> simp [plus,plusData,spin,Matrix.mul_apply,hx]

theorem spin_minus_entry (i : Fin 6) (x y : SS.BitString 6) :
    (spin*minus i) x y=(spinSign x : ℂ)*(minusData i (SS.complement x) y : ℂ) := by
  simp [spin,spinData,minus,Matrix.mul_apply]

theorem transpose_identities (i : Fin 6) :
    (plus i*spin).transpose=spin*minus i ∧ spin*minus i=-(plus i*spin) := by
  constructor
  · ext x y
    simp only [Matrix.transpose_apply,plus_spin_entry,spin_minus_entry]
    exact_mod_cast (transpose_data i x y).1
  · ext x y
    simp only [Matrix.neg_apply,plus_spin_entry,spin_minus_entry]
    exact_mod_cast (transpose_data i x y).2

theorem spin_tensor : spin=tensorKernel (fun _ : Fin 6 => pauli 2) := by
  ext x y
  have h := congrFun (spinJ_tensor (ket y)) x
  simpa [spin,spinData,spinJ,ket,Matrix.mulVec,dotProduct,apply_ite,eq_comm] using h

end MainTheory.Orbit8LadderMatrices
