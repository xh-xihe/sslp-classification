import MainTheory.OrderEightSupportDisplays
import SixQubit.Orbit53
import SixQubit.Orbit54
import SixQubit.Orbit55
import SixQubit.Orbit56

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.OrderSixSupportDisplays
open MainTheory.OrderEightSupportDisplays (bits)

def bottom53 : Fin 10 → SS.BitString 6 := fun i => bits (![0,60,58,6,49,41,25,55,47,31] i)
def top53 : Fin 10 → SS.BitString 6 := fun i => SS.complement (bottom53 i)
theorem bottom_image53 : Finset.univ.image bottom53=SixQubit.Orbit53.S0 := by decide +kernel
theorem top_image53 : Finset.univ.image top53=SixQubit.Orbit53.S1 := by decide +kernel
theorem angle_sum53 : (∑ j,(SixQubit.Orbit53.av j).val)=13 ∧
    (∑ j,SixQubit.Orbit53.av j)=1 := by decide +kernel
theorem complement53 : SixQubit.Orbit53.S1=SixQubit.Orbit53.S0.image SS.complement := by decide +kernel
theorem bottom_injective53 : Function.Injective bottom53 := by decide +kernel
theorem top_injective53 : Function.Injective top53 := by decide +kernel

def bottom54 : Fin 9 → SS.BitString 6 := fun i => bits (![0,60,58,54,14,33,17,47,31] i)
def top54 : Fin 9 → SS.BitString 6 := fun i => SS.complement (bottom54 i)
theorem bottom_image54 : Finset.univ.image bottom54=SixQubit.Orbit54.S0 := by decide +kernel
theorem top_image54 : Finset.univ.image top54=SixQubit.Orbit54.S1 := by decide +kernel
theorem angle_sum54 : (∑ j,(SixQubit.Orbit54.av j).val)=13 ∧
    (∑ j,SixQubit.Orbit54.av j)=1 := by decide +kernel
theorem complement54 : SixQubit.Orbit54.S1=SixQubit.Orbit54.S0.image SS.complement := by decide +kernel
theorem bottom_injective54 : Function.Injective bottom54 := by decide +kernel
theorem top_injective54 : Function.Injective top54 := by decide +kernel

def bottom55 : Fin 11 → SS.BitString 6 := fun i => bits (![0,60,42,26,38,22,49,9,5,47,31] i)
def top55 : Fin 11 → SS.BitString 6 := fun i => SS.complement (bottom55 i)
theorem bottom_image55 : Finset.univ.image bottom55=SixQubit.Orbit55.S0 := by decide +kernel
theorem top_image55 : Finset.univ.image top55=SixQubit.Orbit55.S1 := by decide +kernel
theorem angle_sum55 : (∑ j,(SixQubit.Orbit55.av j).val)=13 ∧
    (∑ j,SixQubit.Orbit55.av j)=1 := by decide +kernel
theorem complement55 : SixQubit.Orbit55.S1=SixQubit.Orbit55.S0.image SS.complement := by decide +kernel
theorem bottom_injective55 : Function.Injective bottom55 := by decide +kernel
theorem top_injective55 : Function.Injective top55 := by decide +kernel

def bottom56 : Fin 10 → SS.BitString 6 := fun i => bits (![0,28,50,42,38,49,41,37,3,31] i)
def top56 : Fin 10 → SS.BitString 6 := fun i => SS.complement (bottom56 i)
theorem bottom_image56 : Finset.univ.image bottom56=SixQubit.Orbit56.S0 := by decide +kernel
theorem top_image56 : Finset.univ.image top56=SixQubit.Orbit56.S1 := by decide +kernel
theorem angle_sum56 : (∑ j,(SixQubit.Orbit56.av j).val)=13 ∧
    (∑ j,SixQubit.Orbit56.av j)=1 := by decide +kernel
theorem complement56 : SixQubit.Orbit56.S1=SixQubit.Orbit56.S0.image SS.complement := by decide +kernel
theorem bottom_injective56 : Function.Injective bottom56 := by decide +kernel
theorem top_injective56 : Function.Injective top56 := by decide +kernel

end MainTheory.OrderSixSupportDisplays
