import MainTheory.Generated.OrbitTableNumericData
import SixQubit.Orbit45Real

set_option autoImplicit false
set_option maxRecDepth 20000

namespace MainTheory.SupplementSummaryDisplays

open MainTheory.Generated.OrbitTableNumericData

theorem orbit45_record : paperQ 44=6 ∧ paperM 44=2 ∧
    SixQubit.Orbit45Real.av=![1,1,2,3,4,4] ∧ (6 : ℕ)/2=3 := ⟨rfl,rfl,rfl,rfl⟩

theorem parity_records : ∀ i : Fin 4,
    paperQ (i.castLE (by decide))=2 ∧ paperM (i.castLE (by decide))=2 ∧
    paperAngle (i.castLE (by decide))=(![![0,0,0,1,1,1],![0,0,1,1,1,1],
      ![0,1,1,1,1,1],![1,1,1,1,1,1]] i) := by decide +kernel

theorem outer_sum :
    (∑ q ∈ Finset.Icc 2 9,(q.divisors.card-1)*Nat.choose (q+5) 6)=13877 := by decide +kernel

end MainTheory.SupplementSummaryDisplays
