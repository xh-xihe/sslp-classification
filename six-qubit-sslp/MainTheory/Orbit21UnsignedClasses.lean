import SixQubit.Orbit21Coef

/-! Unsigned Pauli classes under exactly the two displayed orbit-21 symmetries. -/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace MainTheory.Orbit21UnsignedClasses

def gMask : ℕ := 39
def conjugateZ (x z : ℕ) : ℕ := z ^^^ (x &&& gMask)
def multiplyG (z : ℕ) : ℕ := z ^^^ gMask
def commutesG (x : ℕ) : Bool := SixQubit.Orbit21Coef.pc (x &&& gMask) % 2 == 0
def representative (x z : ℕ) : Bool :=
  z ≤ conjugateZ x z && z ≤ multiplyG z && z ≤ multiplyG (conjugateZ x z)

def classes : Finset (ℕ × ℕ) :=
  ((Finset.range 64).product (Finset.range 64)).filter
    (fun e => commutesG e.1 && representative e.1 e.2)

theorem orbit_operations : ∀ x < 64, ∀ z < 64,
    conjugateZ x (conjugateZ x z) = z ∧
    multiplyG (multiplyG z) = z ∧
    conjugateZ x (multiplyG z) = multiplyG (conjugateZ x z) := by
  decide +kernel

theorem representative_exists : ∀ x < 64, ∀ z < 64,
    ∃ z' ∈ [z,conjugateZ x z,multiplyG z,multiplyG (conjugateZ x z)],
      representative x z' = true := by decide +kernel

theorem classes_count : classes.card = 640 := by decide +kernel

end MainTheory.Orbit21UnsignedClasses
