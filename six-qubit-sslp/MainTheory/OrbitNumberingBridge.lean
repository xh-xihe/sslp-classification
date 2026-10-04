import MainTheory.Generated.OrbitTableRecords

/-! # The paper table and the finite-directory numbering agree -/

namespace MainTheory.OrbitNumberingBridge

open MainTheory.Generated.OrbitTableRecords
open MainTheory.Generated.FiniteOrbitBase

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Every table row maps to the key with its displayed one-based paper id. -/
theorem paperOrbitId_paperKey :
    ∀ i : Fin 66, paperOrbitId (paperKey i) = i.val + 1 := by decide

theorem paperKey_injective : Function.Injective paperKey := by decide

theorem paperKey_surjective : Function.Surjective paperKey := by decide

/-- A bijection, rather than two unrelated lists of integer labels. -/
noncomputable def paperKeyEquiv : Fin 66 ≃ Fin 66 :=
  Equiv.ofBijective paperKey ⟨paperKey_injective, paperKey_surjective⟩

theorem paperKeyEquiv_id (i : Fin 66) :
    paperOrbitId (paperKeyEquiv i) = i.val + 1 := paperOrbitId_paperKey i

end MainTheory.OrbitNumberingBridge
