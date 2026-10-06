import Mathlib

/-! # Finite Kraus channels and genuine code-operator recovery

Channels act on every complex matrix by the usual Kraus sum.  Trace
preservation and positivity after adjoining every finite ancilla are proved
from the Kraus normalization; recovery is an equality of actual channel
actions on all encoded operators.
-/

namespace MainTheory.FiniteKrausChannel

open scoped Matrix Kronecker ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

variable {I J H G L : Type*} [Fintype I] [Fintype J]
  [Fintype H] [Fintype G] [Fintype L]

def action (E : I → Matrix G H ℂ) (X : Matrix H H ℂ) : Matrix G G ℂ :=
  ∑ i, E i * X * (E i).conjTranspose

def TracePreserving [DecidableEq H] (E : I → Matrix G H ℂ) : Prop :=
  ∑ i, (E i).conjTranspose * E i = 1

theorem action_add (E : I → Matrix G H ℂ) (X Y : Matrix H H ℂ) :
    action E (X + Y) = action E X + action E Y := by
  simp [action, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]

theorem action_smul (E : I → Matrix G H ℂ) (z : ℂ) (X : Matrix H H ℂ) :
    action E (z • X) = z • action E X := by
  simp [action, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]

theorem action_sum {T : Type*} [Fintype T] (E : I → Matrix G H ℂ) (X : T → Matrix H H ℂ) :
    action E (∑ t, X t) = ∑ t, action E (X t) := by
  simp only [action, Matrix.mul_sum, Matrix.sum_mul]
  rw [Finset.sum_comm]

theorem trace_action [DecidableEq H] (E : I → Matrix G H ℂ)
    (hE : TracePreserving E) (X : Matrix H H ℂ) :
    Matrix.trace (action E X) = Matrix.trace X := by
  calc
    Matrix.trace (action E X) = ∑ i, Matrix.trace ((E i).conjTranspose * E i * X) := by
      simp only [action, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun i _ => Matrix.trace_mul_cycle _ _ _
    _ = Matrix.trace ((∑ i, (E i).conjTranspose * E i) * X) := by
      simp only [Matrix.sum_mul, Matrix.trace_sum]
    _ = Matrix.trace X := by rw [hE, Matrix.one_mul]

theorem action_posSemidef (E : I → Matrix G H ℂ) {X : Matrix H H ℂ}
    (hX : X.PosSemidef) : (action E X).PosSemidef := by
  classical
  unfold action
  apply Finset.sum_induction
  · intro A B hA hB
    exact hA.add hB
  · exact Matrix.PosSemidef.zero
  · intro i _
    exact hX.mul_mul_conjTranspose_same (E i)

/-- The same channel with an arbitrary finite ancilla left untouched. -/
def amplify (E : I → Matrix G H ℂ) (A : Type*) [Fintype A] [DecidableEq A] :
    I → Matrix (G × A) (H × A) ℂ := fun i => E i ⊗ₖ (1 : Matrix A A ℂ)

/-- Complete positivity for every finite ancillary system. -/
theorem action_completely_positive (E : I → Matrix G H ℂ)
    (A : Type*) [Fintype A] [DecidableEq A]
    (X : Matrix (H × A) (H × A) ℂ) (hX : X.PosSemidef) :
    (action (amplify E A) X).PosSemidef := action_posSemidef _ hX

theorem action_comp (R : J → Matrix L G ℂ) (E : I → Matrix G H ℂ)
    (X : Matrix H H ℂ) :
    action R (action E X) = action (fun p : J × I => R p.1 * E p.2) X := by
  simp only [action, Matrix.mul_sum, Matrix.sum_mul, Fintype.sum_prod_type,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Exact recovery of the error channel on all logical operators, including
coherences.  `V` is the code's physical encoding matrix. -/
def Recovers (V : Matrix H L ℂ) (E : I → Matrix H H ℂ) (R : J → Matrix H H ℂ) : Prop :=
  ∀ X : Matrix L L ℂ,
    action R (action E (V * X * V.conjTranspose)) = V * X * V.conjTranspose

/-- The actual Knill--Laflamme scalar compression equations. -/
def KnillLaflamme [DecidableEq L] (V : Matrix H L ℂ) (E : I → Matrix H H ℂ) : Prop :=
  ∃ c : Matrix I I ℂ, ∀ i j,
    V.conjTranspose * (E i).conjTranspose * E j * V = c i j • 1

end

end MainTheory.FiniteKrausChannel
