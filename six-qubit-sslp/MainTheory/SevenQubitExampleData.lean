import SS.HilbertKL

/-! Exact finite data for the seven-qubit rational-replacement example. -/
namespace MainTheory.SevenQubitExampleData

open scoped BigOperators
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000

def num (x : SS.BitString 7) : ℕ := ∑ j : Fin 7, if x j then 2 ^ j.val else 0
def nbit (m : ℕ) : SS.BitString 7 := fun j => Nat.testBit m j.val

theorem nbit_num : ∀ x, nbit (num x) = x := by decide +kernel
theorem num_lt : ∀ x, num x < 128 := by decide +kernel

theorem mask_low_weight : ∀ z : SS.BitString 7, SS.hammingWt z ≤ 1 →
    z = (fun _ => false) ∨ ∃ j : Fin 7, z = SS.stdBasis j := by decide +kernel

def probability (k : Fin 2) (x : SS.BitString 7) : ℚ :=
  if k = 0 then
    if num x = 0 ∨ num x = 15 then 1 / 6
    else if num x = 112 ∨ num x = 127 then 1 / 3 else 0
  else if num x ∈ ({51, 60, 101, 105, 86, 90} : Finset ℕ) then 1 / 6 else 0

theorem probability_nonneg : ∀ k x, 0 ≤ probability k x := by decide +kernel
theorem probability_sum : ∀ k, ∑ x, probability k x = 1 := by decide +kernel
theorem probability_disjoint : ∀ k l, k ≠ l → ∀ x,
    probability k x = 0 ∨ probability l x = 0 := by decide +kernel

def mean : Fin 7 → ℚ := ![1/2, 1/2, 1/2, 1/2, 2/3, 2/3, 2/3]

theorem first_moments : ∀ k j,
    (∑ x, probability k x * (if x j then 1 else 0 : ℚ)) = mean j := by
  decide +kernel

theorem single_flip_disjoint : ∀ k l (j : Fin 7) x,
    probability k x = 0 ∨ probability l (SS.bxor x (SS.stdBasis j)) = 0 := by
  decide +kernel

def direction : Fin 7 → ℤ := ![1, -1, 0, 0, 1, -1, 0]
def weight (h : Fin 7 → ℤ) (x : SS.BitString 7) : ℤ :=
  ∑ j, if x j then h j else 0

theorem direction_zero : ∀ k x, probability k x ≠ 0 → weight direction x = 0 := by
  decide +kernel
theorem direction_mean : ∑ j, (direction j : ℚ) * mean j = 0 := by decide +kernel

def character (z x : SS.BitString 7) : ℚ := if SS.bdot z x then -1 else 1

theorem diagonal_low_weight : ∀ z : SS.BitString 7, SS.hammingWt z ≤ 1 →
    (∑ x, probability 0 x * character z x) =
      ∑ x, probability 1 x * character z x := by decide +kernel

def zz12 : SS.PauliString 7 :=
  ⟨fun _ => false, fun j => decide (j = 0 ∨ j = 1)⟩

theorem zz12_data : zz12.wt = 2 ∧ zz12.numY = 0 ∧
    (∑ x, probability 0 x * character zz12.z x) = 1 ∧
    (∑ x, probability 1 x * character zz12.z x) = -1/3 := by decide +kernel

end MainTheory.SevenQubitExampleData
