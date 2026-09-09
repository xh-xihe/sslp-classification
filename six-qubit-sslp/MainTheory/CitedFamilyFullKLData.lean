import MainTheory.CitedFamilyMomentData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace MainTheory.CitedFamilyFullKLData

open SixQubit.Realize MainTheory.CitedFamilyMomentData

theorem checked : ∀ m < 64,∀ z < 64,
    (⟨nbit m,nbit z⟩ : SS.PauliString 6).wt ≤ 2 →
    ∀ i j : Fin 2,∀ b b' : Bool,
    zmat (base i b) (base j b') L (nbit m) (nbit z)=
      if i=j then zmat (base 0 b) (base 0 b') L (nbit m) (nbit z)
      else ZQ.zero := by decide +kernel

end MainTheory.CitedFamilyFullKLData
