import MainTheory.OrderEightSupportDisplays
import SixQubit.Orbit57
import SixQubit.Orbit58
import SixQubit.Orbit59
import SixQubit.Orbit60
import SixQubit.Orbit61

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace MainTheory.OrderSevenSupportDisplays
open MainTheory.OrderEightSupportDisplays (bits)

def bottom57 : Fin 7 → SS.BitString 6 := fun i => bits (![0,60,58,57,55,47,31] i)
def top57 : Fin 7 → SS.BitString 6 := fun i => SS.complement (bottom57 i)

theorem bottom_image57 : Finset.univ.image bottom57=SixQubit.Orbit57.S0 := by decide +kernel
theorem top_image57 : Finset.univ.image top57=SixQubit.Orbit57.S1 := by decide +kernel
theorem angle_sum57 : (∑ j,SixQubit.Orbit57.av j)=1 := by decide +kernel
theorem complement57 : SixQubit.Orbit57.S1=SixQubit.Orbit57.S0.image SS.complement := by decide +kernel

def bottom58 : Fin 9 → SS.BitString 6 := fun i => bits (![0,60,58,38,22,49,9,47,31] i)
def top58 : Fin 9 → SS.BitString 6 := fun i => SS.complement (bottom58 i)

theorem bottom_image58 : Finset.univ.image bottom58=SixQubit.Orbit58.S0 := by decide +kernel
theorem top_image58 : Finset.univ.image top58=SixQubit.Orbit58.S1 := by decide +kernel
theorem angle_sum58 : (∑ j,SixQubit.Orbit58.av j)=1 := by decide +kernel
theorem complement58 : SixQubit.Orbit58.S1=SixQubit.Orbit58.S0.image SS.complement := by decide +kernel

def bottom59 : Fin 7 → SS.BitString 6 := fun i => bits (![0,56,52,50,49,47,31] i)
def top59 : Fin 7 → SS.BitString 6 := fun i => SS.complement (bottom59 i)

theorem bottom_image59 : Finset.univ.image bottom59=SixQubit.Orbit59.S0 := by decide +kernel
theorem top_image59 : Finset.univ.image top59=SixQubit.Orbit59.S1 := by decide +kernel
theorem angle_sum59 : (∑ j,SixQubit.Orbit59.av j)=1 := by decide +kernel
theorem complement59 : SixQubit.Orbit59.S1=SixQubit.Orbit59.S0.image SS.complement := by decide +kernel

def bottom60 : Fin 9 → SS.BitString 6 := fun i => bits (![0,60,50,42,38,49,41,37,31] i)
def top60 : Fin 9 → SS.BitString 6 := fun i => SS.complement (bottom60 i)

theorem bottom_image60 : Finset.univ.image bottom60=SixQubit.Orbit60.S0 := by decide +kernel
theorem top_image60 : Finset.univ.image top60=SixQubit.Orbit60.S1 := by decide +kernel
theorem angle_sum60 : (∑ j,SixQubit.Orbit60.av j)=1 := by decide +kernel
theorem complement60 : SixQubit.Orbit60.S1=SixQubit.Orbit60.S0.image SS.complement := by decide +kernel

def bottom61 : Fin 9 → SS.BitString 6 := fun i => bits (![0,28,26,38,49,41,5,3,31] i)
def top61 : Fin 9 → SS.BitString 6 := fun i => SS.complement (bottom61 i)

theorem bottom_image61 : Finset.univ.image bottom61=SixQubit.Orbit61.S0 := by decide +kernel
theorem top_image61 : Finset.univ.image top61=SixQubit.Orbit61.S1 := by decide +kernel
theorem angle_sum61 : (∑ j,SixQubit.Orbit61.av j)=1 := by decide +kernel
theorem complement61 : SixQubit.Orbit61.S1=SixQubit.Orbit61.S0.image SS.complement := by decide +kernel

end MainTheory.OrderSevenSupportDisplays
