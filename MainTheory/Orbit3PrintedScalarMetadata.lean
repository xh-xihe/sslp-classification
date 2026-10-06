import MainTheory.Orbit3PauliZeros
import MainTheory.Orbit3CategoryBridge

/-! Exact scalar category sizes, quadratic-label counts, and the printed LP witness. -/

namespace MainTheory.Orbit3PrintedScalarMetadata

open SixQubit.Generated MainTheory.Orbit3PauliZeros
open MainTheory.PhysicalPauliCategories MainTheory.Orbit3CategoryShift
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def size (c : ℕ × ℕ × ℕ) : ℕ :=
  3^c.1 * (Nat.factorial 5/(Nat.factorial c.2.1*Nat.factorial c.2.2*
    Nat.factorial (5-c.2.1-c.2.2))) * 2^c.2.2

theorem printed_size : ∀ e : Fin 42,
    Orbit3CategoryRows.errorSize e=size (Orbit3CategoryRows.errorCategory e) := by
  decide +kernel

theorem even_categories :
    (Finset.univ.filter (fun e : Fin 42 =>
      (Orbit3CategoryRows.errorCategory e).2.2%2=0)).card=24 := by decide +kernel

theorem zero_category_sizes : ∀ k : Fin 5,
    size (Orbit3Scalar.categories (Orbit3Scalar.zeroIndex k))=![5,40,120,30,10] k := by
  decide +kernel

def diagonalLabels (r : Fin 4096) : Prop :=
  (shift (decode r)).wt≤2 ∧ SS.bdot MainTheory.OrderTwoScalarBridge.orbit3Mask
    (decode r).x=false

def crossLabels (r : Fin 4096) : Prop :=
  ((decode r).wt≤2 ∨ (shift (decode r)).wt≤2) ∧
    SS.bdot MainTheory.OrderTwoScalarBridge.orbit3Mask (decode r).x=true

def categoryLabels (r : Fin 4096) : Prop :=
  ∃ k : Fin 5, category (decode r)=Orbit3Scalar.categories (Orbit3Scalar.zeroIndex k)

instance (r) : Decidable (diagonalLabels r) := by unfold diagonalLabels; infer_instance
instance (r) : Decidable (crossLabels r) := by unfold crossLabels; infer_instance
instance (r) : Decidable (categoryLabels r) := by unfold categoryLabels; infer_instance

theorem constrained_union (r : Fin 4096) : Constrained (decode r) ↔
    diagonalLabels r ∨ crossLabels r ∨ categoryLabels r := by
  unfold Constrained diagonalLabels crossLabels categoryLabels
  cases SS.bdot MainTheory.OrderTwoScalarBridge.orbit3Mask (decode r).x <;> simp_all [or_assoc]

theorem physical_category_sizes : ∀ e : Fin 42,
    (Finset.univ.filter (fun r : Fin 4096 =>
      category (decode r)=Orbit3CategoryRows.errorCategory e)).card=
      Orbit3CategoryRows.errorSize e := by
  intro e
  fin_cases e
  all_goals decide +kernel

theorem constraint_counts :
    (Finset.univ.filter diagonalLabels).card=74 ∧
    (Finset.univ.filter crossLabels).card=160 ∧
    (Finset.univ.filter categoryLabels).card=205 ∧
    (Finset.univ.filter (fun r =>
      (diagonalLabels r ∨ crossLabels r) ∧ categoryLabels r)).card=10 ∧
    (Finset.univ.filter (fun r => Constrained (decode r))).card=429 := by
  decide +kernel

def witness : Fin 24 → ℚ :=
  ![1,0,0,0,0,0,0,0,4,0,1,2,0,0,0,1,0,0,1,6,7,2,6,1]

theorem witness_nonnegative : ∀ c, 0 ≤ witness c := by decide +kernel

theorem witness_equalities : ∀ i : Fin 43,
    (∑ c : Fin 24, Orbit3Scalar.equalities i c*witness c)=Orbit3Scalar.rhs i := by
  decide +kernel

theorem witness_inequalities : ∀ i : Fin 84,
    0 ≤ ∑ c : Fin 24, Orbit3Scalar.positive i c*witness c := by decide +kernel

theorem witness_enumerator : ∀ w : Fin 7,
    (∑ c : Fin 24, if (Orbit3Scalar.categories c).1+
      (Orbit3Scalar.categories c).2.1+(Orbit3Scalar.categories c).2.2=w.val
      then witness c else 0)=![1,0,0,1,12,15,3] w := by decide +kernel

end MainTheory.Orbit3PrintedScalarMetadata
