import SixQubit.Orbit64
import SixQubit.Orbit65

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderEightSupportDisplays

def bits (n : ℕ) : SS.BitString 6 := fun i => Nat.testBit n (5-i.val)

def bottomA : Fin 7 → SS.BitString 6 := fun i => bits (![0,60,58,54,49,47,31] i)
def bottomB : Fin 8 → SS.BitString 6 := fun i => bits (![0,60,26,38,49,41,5,31] i)
def topA : Fin 7 → SS.BitString 6 := fun i => SS.complement (bottomA i)
def topB : Fin 8 → SS.BitString 6 := fun i => SS.complement (bottomB i)

theorem angle_A : SixQubit.Orbit64.av=![1,1,3,3,3,6] := rfl
theorem angle_B : SixQubit.Orbit65.av=![1,2,2,3,4,5] := rfl

theorem angle_sums : (∑ j,(SixQubit.Orbit64.av j).val)=17 ∧
    (∑ j,(SixQubit.Orbit65.av j).val)=17 ∧
    (∑ j,SixQubit.Orbit64.av j)=1 ∧ (∑ j,SixQubit.Orbit65.av j)=1 := by decide +kernel

theorem bottom_A : SixQubit.Orbit64.S0=Finset.univ.image bottomA := by decide +kernel
theorem top_A : SixQubit.Orbit64.S1=([32,16,14,9,5,3,63].map bits).toFinset := by decide +kernel
theorem bottom_B : SixQubit.Orbit65.S0=Finset.univ.image bottomB := by decide +kernel
theorem top_B : SixQubit.Orbit65.S1=([63,3,37,25,14,22,58,32].map bits).toFinset := by decide +kernel

theorem complement_A : SixQubit.Orbit64.S1=SixQubit.Orbit64.S0.image SS.complement := rfl
theorem complement_B : SixQubit.Orbit65.S1=SixQubit.Orbit65.S0.image SS.complement := by decide +kernel

theorem topA_image : Finset.univ.image topA=SixQubit.Orbit64.S1 := by decide +kernel
theorem topB_image : Finset.univ.image topB=SixQubit.Orbit65.S1 := by decide +kernel

theorem support_sizes : SixQubit.Orbit64.S0.card=7 ∧ SixQubit.Orbit64.S1.card=7 ∧
    SixQubit.Orbit65.S0.card=8 ∧ SixQubit.Orbit65.S1.card=8 := by decide +kernel

end MainTheory.OrderEightSupportDisplays
