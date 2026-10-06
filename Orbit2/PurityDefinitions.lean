import Orbit2.TensorPauli

/-! A finite, structural sum-of-squares reduction of the complementary-purity
step. Connecting the masses and purity equations to Encoder is a separate
obligation; no such connection is assumed as an axiom here. -/
namespace Orbit2.PurityReduction
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

abbrev Paulis := Label 7
def G : Paulis := ![3,0,0,3,3,3,3]
def partner (p : Paulis) : Paulis := product p G
def supported (p : Paulis) (S : Fin 7 → Bool) : Bool :=
  decide (∀ i, p i = 0 ∨ S i)
def A : Fin 7 → Bool := fun i => decide (3 ≤ i.val)
def B : Fin 7 → Bool := fun i => decide (i.val = 1 ∨ i.val = 2)
def RA : Fin 7 → Bool := fun i => decide (i.val = 0 ∨ 3 ≤ i.val)
def indicator (b : Bool) : ℤ := if b then 1 else 0

/-- Twice Eq(purity-2) minus twice Eq(purity-1) minus Eq(B versus RA). -/
def purityCoefficient (p : Paulis) : ℤ :=
  2 * (∑ i : Fin 4, indicator (supported p (fun j => RA j && decide (j.val ≠ i.val+3)))) -
  4 * (∑ i : Fin 4, indicator (supported p (fun j => B j || decide (j.val = i.val+3)))) -
  2 * indicator (supported p A) - indicator (supported p RA) +
  12 * indicator (supported p B)

def spectatorMass (p : Paulis) : Bool := supported p B && decide (p ≠ fun _ => 0)
def mixedMass (p : Paulis) : Bool :=
  decide (p 0 = 0 ∧ (p 1 ≠ 0 ∨ p 2 ≠ 0) ∧
    (∑ i : Fin 4, if p ⟨i.val+3,by omega⟩ = 0 then 0 else 1 : ℕ) = 1 ∧
      ∀ i : Fin 4, p ⟨i.val+3,by omega⟩ = 0 ∨ p ⟨i.val+3,by omega⟩ = 3)
def transverseFourMass (p : Paulis) : Bool :=
  supported p A && decide (∀ i : Fin 4,
    p ⟨i.val+3,by omega⟩ = 1 ∨ p ⟨i.val+3,by omega⟩ = 2)
def targetCoefficient (p : Paulis) : ℤ :=
  indicator (spectatorMass p) + indicator (mixedMass p) + indicator (transverseFourMass p)

def zeroKL (p : Paulis) : Bool := decide (p 0 ≠ 0 ∧
  (∑ i : Fin 6, if p i.succ = 0 then 0 else 1 : ℕ) ≤ 2)
def zeroParity (p : Paulis) : Bool := decide
  (((∑ i : Fin 7, if (i.val = 0 ∨ (3 ≤ i.val)) ∧ (p i = 1 ∨ p i = 2)
    then 1 else 0) : ℕ) % 2 = 1)
def forbidden (p : Paulis) : Bool := zeroKL p || zeroParity p

def packed (r b c : Fin 4) (a : Label 4) : Paulis := ![r,b,c,a 0,a 1,a 2,a 3]


end Orbit2.PurityReduction
