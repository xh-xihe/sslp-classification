import Mathlib

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace MainTheory.Orbit36SupportGraphs

def pairs : Fin 6 → Fin 4 × Fin 4 := ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
def edge (mask : Fin 64) (i j : Fin 4) : Prop :=
  ∃ e : Fin 6, mask.val.testBit e.val = true ∧
    (pairs e = (i,j) ∨ pairs e = (j,i))
instance (mask : Fin 64) (i j : Fin 4) : Decidable (edge mask i j) := by
  unfold edge
  infer_instance
def degree (mask : Fin 64) (i : Fin 4) : ℕ := (Finset.univ.filter (edge mask i)).card

theorem mask_classification : ∀ mask : Fin 64, (∀ i, 2 ≤ degree mask i) →
    mask = 63 ∨ mask ∈ ({31,47,55,59,61,62} : Finset (Fin 64)) ∨
      mask ∈ ({30,45,51} : Finset (Fin 64)) := by decide +kernel

theorem graph_classification : ∀ mask : Fin 64, (∀ i, 2 ≤ degree mask i) →
    mask = 63 ∨ ∃ p : Equiv.Perm (Fin 4),
      (∀ i j, edge mask i j ↔ edge 31 (p i) (p j)) ∨
      (∀ i j, edge mask i j ↔ edge 51 (p i) (p j)) := by decide +kernel

noncomputable def activeEdges (C : Matrix (Fin 4) (Fin 4) ℂ) : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2 ∧ C ij.1 ij.2 ≠ 0)

theorem mem_activeEdges (C : Matrix (Fin 4) (Fin 4) ℂ) (i j : Fin 4) :
    (i,j) ∈ activeEdges C ↔ i < j ∧ C i j ≠ 0 := by
  classical
  simp [activeEdges]

end MainTheory.Orbit36SupportGraphs
