import Orbit2.TensorPauli

namespace Orbit2.FiveQubit
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def flipSite (p : Fin 4) (s : Fin 2) : Fin 2 :=
  if p = 1 ∨ p = 2 then (if s = 0 then 1 else 0) else s
def flip (p : Label 5) (s : Fin 5 → Fin 2) : Fin 5 → Fin 2 :=
  fun i => flipSite (p i) (s i)
def amplitude (p : Label 5) (s : Fin 5 → Fin 2) : GaussianInt :=
  ∏ i, localG (p i) (s i) (flip p s i)
def act (p : Label 5) (v : (Fin 5 → Fin 2) → GaussianInt) (s : Fin 5 → Fin 2) : GaussianInt :=
  amplitude p s * v (flip p s)
def weight (p : Label 5) : ℕ := ∑ i, if p i = 0 then 0 else 1

def seed (j : Fin 2) (s : Fin 5 → Fin 2) : GaussianInt :=
  ![![![![![![⟨0, 2⟩, ⟨-2, 0⟩], ![⟨-2, 0⟩, ⟨0, 2⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩]]], ![![![⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-2, 0⟩, ⟨0, -2⟩], ![⟨0, 2⟩, ⟨2, 0⟩]]]], ![![![![⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨-2, 0⟩, ⟨0, 2⟩], ![⟨0, -2⟩, ⟨2, 0⟩]]], ![![![⟨0, -2⟩, ⟨-2, 0⟩], ![⟨-2, 0⟩, ⟨0, -2⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩]]]]], ![![![![![⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, 2⟩, ⟨2, 0⟩], ![⟨2, 0⟩, ⟨0, 2⟩]]], ![![![⟨2, 0⟩, ⟨0, -2⟩], ![⟨0, 2⟩, ⟨-2, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩]]]], ![![![![⟨2, 0⟩, ⟨0, 2⟩], ![⟨0, -2⟩, ⟨-2, 0⟩]], ![![⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩]]], ![![![⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩]], ![![⟨0, -2⟩, ⟨2, 0⟩], ![⟨2, 0⟩, ⟨0, -2⟩]]]]]] j (s 0) (s 1) (s 2) (s 3) (s 4)

/-- Every Pauli of weight at most two has exactly zero compression, except I.
The normalization is 64 because the logical columns are seed/8. -/
theorem pure_KL_G : ∀ p : Label 5, weight p ≤ 2 → ∀ j k : Fin 2,
    (∑ s, star (seed j s) * act p (seed k) s) =
      if p = (fun _ => 0) ∧ j = k then 64 else 0 := by
  decide +kernel

theorem logical_G : ∀ j s, act ![3,3,3,0,0] (seed j) s =
    (if j = 0 then 1 else -1) * seed j s := by
  decide +kernel

end Orbit2.FiveQubit
