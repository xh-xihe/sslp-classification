import MainTheory.CodeSpec
import MainTheory.FiveQubitRationalization

/-! The literal five-qubit basis in arXiv:2504.20847v1, Appendix B.1.
Bit zero is the leftmost printed bit. Integer certificates are transported
to genuine complex Pauli matrix elements. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace MainTheory.FiveQubitPerfectCore

def bits (m : ℕ) : SS.BitString 5 := fun i => Nat.testBit m (4-i.val)
def number (x : SS.BitString 5) : ℕ :=
  (if x 0 then 16 else 0)+(if x 1 then 8 else 0)+(if x 2 then 4 else 0)+
  (if x 3 then 2 else 0)+(if x 4 then 1 else 0)

theorem bits_number : ∀ x, bits (number x)=x := by decide
theorem number_lt : ∀ x, number x<32 := by decide

def coefficients : Fin 2 → Fin 32 → ℤ :=
  ![![1,0,0,-1,0,1,-1,0,0,1,1,0,-1,0,0,-1,
      0,-1,1,0,1,0,0,-1,-1,0,0,-1,0,-1,-1,0],
    ![0,1,1,0,1,0,0,1,1,0,0,-1,0,-1,1,0,
      1,0,0,1,0,-1,-1,0,0,1,-1,0,1,0,0,-1]]

def raw (i : Fin 2) (x : SS.BitString 5) : ℤ := coefficients i ⟨number x,number_lt x⟩

def correlation (i j : Fin 2) (P : SS.PauliString 5) : ℤ :=
  ∑ x, (if SS.bdot P.z x then -1 else 1)*raw i (SS.bxor x P.x)*raw j x

theorem raw_gram : ∀ i j, (∑ x,raw i x*raw j x)=if i=j then 16 else 0 := by decide

theorem raw_low : ∀ m < 32, ∀ z < 32,
    (⟨bits m,bits z⟩ : SS.PauliString 5).wt ≤ 2 → ∀ i j,
    correlation i j ⟨bits m,bits z⟩ = if m=0 ∧ z=0 ∧ i=j then 16 else 0 := by
  decide

theorem correlation_low (P : SS.PauliString 5) (hP : P.wt ≤ 2) (i j : Fin 2) :
    correlation i j P = if number P.x=0 ∧ number P.z=0 ∧ i=j then 16 else 0 := by
  have h := raw_low (number P.x) (number_lt P.x) (number P.z) (number_lt P.z)
  simp only [bits_number] at h
  exact h hP i j

noncomputable def state (i : Fin 2) : SS.State 5 ℂ := fun x => (1/4 : ℂ)*(raw i x : ℂ)

theorem inner_state (i j : Fin 2) : SS.innerC (state i) (state j)=if i=j then 1 else 0 := by
  calc
    _ = (1/16 : ℂ)*((∑ x,raw i x*raw j x : ℤ) : ℂ) := by
      simp only [SS.innerC,Int.cast_sum,Int.cast_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp [state]
      ring
    _ = _ := by rw [raw_gram]; split_ifs <;> norm_num

theorem pauli_element (i j : Fin 2) (P : SS.PauliString 5) :
    SS.innerC (state i) (SS.pauliAct P (state j)) =
      Complex.I^P.numY*(1/16 : ℂ)*(correlation i j P : ℂ) := by
  rw [SS.innerC_pauliAct,mul_assoc]
  congr 1
  simp only [correlation,Int.cast_sum,Int.cast_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  cases SS.bdot P.z x <;> simp [state,SS.signC] <;> ring

theorem hasDistance_three : SS.HasDistance state 3 := by
  intro P hP
  refine ⟨if number P.x=0 ∧ number P.z=0 then Complex.I^P.numY else 0, ?_⟩
  intro i j
  rw [pauli_element,correlation_low P hP]
  split_ifs <;> simp_all

noncomputable def code : CodeSpec.ExactCode 5 2 3 where
  positiveRank := by norm_num
  frame := ⟨state,inner_state⟩
  hasDistance := hasDistance_three

end MainTheory.FiveQubitPerfectCore
