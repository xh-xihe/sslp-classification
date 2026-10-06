import Orbit2.FiveQubit

namespace Orbit2.SplitSeed
open scoped BigOperators
open Orbit2.TensorPauli
open Orbit2.FiveQubit (flipSite seed)
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

abbrev Bits := Fin 6 → Fin 2
def weight (p : Label 6) : ℕ := ∑ i, if p i = 0 then 0 else 1
def flip (p : Label 6) (s : Bits) : Bits := fun i => flipSite (p i) (s i)
def amplitude (p : Label 6) (s : Bits) : GaussianInt := ∏ i, localG (p i) (s i) (flip p s i)
def act (p : Label 6) (v : Bits → GaussianInt) (s : Bits) : GaussianInt :=
  amplitude p s * v (flip p s)

/-- Spectators are sites 0,1; the split outputs are sites 2,3. -/
def component (r j : Fin 2) (s : Bits) : GaussianInt :=
  if s 2 = r then seed j ![if s 2 = s 3 then 0 else 1, s 4, s 5, s 0, s 1] else 0

def entry (r t : Fin 2) (p : Label 6) (j k : Fin 2) : GaussianInt :=
  ∑ s, star (component r j s) * act p (component t k) s

def splitZ : Label 6 := ![0,0,3,0,0,0]
def splitXX : Label 6 := ![0,0,1,1,0,0]

/-- The complete degree-two KL certificate for arbitrary real a,b. -/
theorem diagonal_zero_component : ∀ p : Label 6, weight p ≤ 2 → ∀ j k,
    entry 0 0 p j k = if j = k ∧ (p = (fun _ => 0) ∨ p = splitZ) then 64 else 0 := by
  decide +kernel

theorem diagonal_one_component : ∀ p : Label 6, weight p ≤ 2 → ∀ j k,
    entry 1 1 p j k = if j = k then
      (if p = (fun _ => 0) then 64 else if p = splitZ then -64 else 0) else 0 := by
  decide +kernel

theorem cross_components : ∀ p : Label 6, weight p ≤ 2 → ∀ j k,
    entry 0 1 p j k + entry 1 0 p j k =
      if j = k ∧ p = splitXX then 128 else 0 := by
  decide +kernel

theorem logical_components : ∀ r j s,
    act ![0,0,3,3,3,3] (component r j) s = (if j = 0 then 1 else -1) * component r j s := by
  decide +kernel

end Orbit2.SplitSeed
