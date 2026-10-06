import MainTheory.OrderEightSupportDisplays
import SixQubit.Orbit26
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderFour26Support
open MainTheory.OrderEightSupportDisplays (bits)
def tailMap (x y z : Bool) : Fin 5 → Bool := ![x,y,z,Bool.xor z (x && y),Bool.xor x y]
def labels : Fin 8 → Fin 3 → Bool :=
  ![![false,false,false],![false,false,true],![true,false,false],![true,false,true],
    ![false,true,false],![false,true,true],![true,true,false],![true,true,true]]
def tailWords : Fin 8 → ℕ := ![0,6,17,23,9,15,26,28]
def bottomAt (b : Bool) (i : Fin 8) : SS.BitString 6 := bits (tailWords i+(if b then 32 else 0))
def topAt (b : Bool) (i : Fin 8) : SS.BitString 6 := bits (31-tailWords i+(if b then 32 else 0))
theorem literal_tail : ∀ i j,tailMap (labels i 0) (labels i 1) (labels i 2) j=
    bottomAt false i j.succ := by decide +kernel
theorem label_bijection : Function.Bijective labels := by decide +kernel
theorem bottom_fiber : Finset.univ.image (fun p : Bool × Fin 8 => bottomAt p.1 p.2)=SixQubit.Orbit26.S0 := by decide +kernel
theorem top_fiber : Finset.univ.image (fun p : Bool × Fin 8 => topAt p.1 p.2)=SixQubit.Orbit26.S1 := by decide +kernel
theorem angle_sum : (∑ j,(SixQubit.Orbit26.av j).val)=9 ∧ (∑ j,SixQubit.Orbit26.av j)=1 := by decide +kernel
def bottom : Fin 16 → SS.BitString 6 := fun i => bits (![0,6,17,23,9,15,26,28,32,38,49,55,41,47,58,60] i)
theorem bottom_image : Finset.univ.image bottom=SixQubit.Orbit26.S0 := by decide +kernel
theorem bottom_injective : Function.Injective bottom := by decide +kernel
def top : Fin 16 → SS.BitString 6 := fun i => bits (![31,25,14,8,22,16,5,3,63,57,46,40,54,48,37,35] i)
theorem top_image : Finset.univ.image top=SixQubit.Orbit26.S1 := by decide +kernel
theorem top_injective : Function.Injective top := by decide +kernel
def index (b : Bool) (i : Fin 8) : Fin 16 := ⟨i.val+(if b then 8 else 0),by split <;> omega⟩
theorem bottom_index : ∀ b i,bottomAt b i=bottom (index b i) := by decide +kernel
theorem top_index : ∀ b i,topAt b i=top (index b i) := by decide +kernel
end MainTheory.OrderFour26Support
