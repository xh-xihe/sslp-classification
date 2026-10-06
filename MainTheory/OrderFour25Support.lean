import MainTheory.OrderEightSupportDisplays
import SixQubit.Orbit25
import MainTheory.SupportKetExpansion

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.OrderFour25Support
open MainTheory.OrderEightSupportDisplays (bits)
def bottom : Fin 12 → SS.BitString 6 := fun i => bits (![0,15,23,27,29,30,32,47,55,59,61,62] i)
theorem bottom_image : Finset.univ.image bottom=SixQubit.Orbit25.S0 := by decide +kernel
theorem bottom_injective : Function.Injective bottom := by decide +kernel
def top : Fin 12 → SS.BitString 6 := fun i => bits (![16,8,4,2,1,31,48,40,36,34,33,63] i)
theorem top_image : Finset.univ.image top=SixQubit.Orbit25.S1 := by decide +kernel
theorem top_injective : Function.Injective top := by decide +kernel
def anchor (b : Bool) : SS.BitString 6 := bits (if b then 32 else 0)
def unit (j : Fin 5) : SS.BitString 6 := bits (2^(4-j.val))
def tail (b : Bool) (j : Fin 5) : SS.BitString 6 := SS.bxor (anchor b) (unit j)
def full (b : Bool) : SS.BitString 6 := bits (if b then 63 else 31)
def hat (b : Bool) (j : Fin 5) : SS.BitString 6 := SS.bxor (full b) (unit j)
theorem bottom_fiber : SixQubit.Orbit25.S0=
    (Finset.univ.image anchor) ∪ (Finset.univ.image fun p : Bool × Fin 5 => hat p.1 p.2) := by decide +kernel
theorem top_fiber : SixQubit.Orbit25.S1=
    (Finset.univ.image full) ∪ (Finset.univ.image fun p : Bool × Fin 5 => tail p.1 p.2) := by decide +kernel
theorem unit_coordinate : ∀ j k,unit j k=decide (k.val=j.val+1) := by decide +kernel
end MainTheory.OrderFour25Support
