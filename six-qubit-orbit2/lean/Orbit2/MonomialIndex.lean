import Orbit2.JExpansion
import Orbit2.Reconstruction

namespace Orbit2.Quartic
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def pairIndexNat (u v : Fin 32) : ℕ :=
  (min u.val v.val) * (65 - min u.val v.val) / 2 + max u.val v.val - min u.val v.val

theorem pairIndex_bound : ∀ u v : Fin 32, pairIndexNat u v < 528 := by decide +kernel

def pairIndex (p : Fin 32 × Fin 32) : Fin 528 :=
  ⟨pairIndexNat p.1 p.2, pairIndex_bound p.1 p.2⟩

theorem pairIndex_mem : ∀ p : Fin 32 × Fin 32, p ∈ orders (pairIndex p) := by decide +kernel

theorem orders_pairIndex : ∀ r : Fin 528,
    (orders r).all (fun p => pairIndex p == r)=true := by decide +kernel

theorem orders_nodup : ∀ r : Fin 528, (orders r).Nodup := by decide +kernel

end Orbit2.Quartic
