import MainTheory.Generated.Orbit31PrintedSupportOrbits

/-! The previously printed twelve-string support is the literal type-two
representative after the physical swap of the first two equal-angle sites. -/
set_option autoImplicit false
namespace MainTheory.Orbit31HistoricalSupport
open MainTheory.OrderEightSupportDisplays (bits)
open MainTheory.Orbit31SupportBase (bottom)
open MainTheory.Orbit31SupportSemantics (maskSet)
open MainTheory.Orbit31TableSymmetry
open MainTheory.Generated.Orbit31PrintedSupportOrbits (representatives)

def oldMask : Fin 65536 := ⟨53055,by decide⟩
def oldSupport : Finset (SS.BitString 6) :=
  {bits 0,bits 3,bits 5,bits 6,bits 28,bits 31,bits 41,bits 42,bits 44,bits 47,bits 49,bits 50}
def swapFirstTwo : Fin 144 := ⟨48,by decide⟩
theorem mask_transport : action swapFirstTwo (representatives ⟨1,by decide⟩)=oldMask := by
  decide +kernel
theorem literal_support : (maskSet oldMask.val).image bottom=oldSupport := by decide +kernel
theorem physical_swap : ∀ x, physicalAction swapFirstTwo x=![x 1,x 0,x 2,x 3,x 4,x 5] := by
  decide +kernel
theorem physical_image : ((maskSet (representatives ⟨1,by decide⟩).val).image bottom).image
    (physicalAction swapFirstTwo)=oldSupport := by decide +kernel

end MainTheory.Orbit31HistoricalSupport
