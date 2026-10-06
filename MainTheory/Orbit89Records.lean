import MainTheory.Generated.OrbitTableNumericData
import SixQubit.Orbit8Real
import SixQubit.Orbit9Real

set_option autoImplicit false

namespace MainTheory.Orbit89Records

open MainTheory.Generated.OrbitTableNumericData

theorem orbit8_record : paperQ 7=3 ∧ paperM 7=3 ∧
    SixQubit.Orbit8Real.av=![1,1,1,1,1,1] := ⟨rfl,rfl,rfl⟩

theorem orbit9_record : paperQ 8=3 ∧ paperM 8=3 ∧
    SixQubit.Orbit9Real.av=![1,1,1,1,1,2] := ⟨rfl,rfl,rfl⟩

end MainTheory.Orbit89Records
