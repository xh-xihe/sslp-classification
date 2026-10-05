import SixQubit.Generated.SpectatorCubicTwirl.Check00
import SixQubit.Generated.SpectatorCubicTwirl.Check01
import SixQubit.Generated.SpectatorCubicTwirl.Check02
import SixQubit.Generated.SpectatorCubicTwirl.Check03
import SixQubit.Generated.SpectatorCubicTwirl.Check04
import SixQubit.Generated.SpectatorCubicTwirl.Check05
import SixQubit.Generated.SpectatorCubicTwirl.Check06
import SixQubit.Generated.SpectatorCubicTwirl.Check07

namespace SixQubit.Generated.SpectatorCubicTwirl
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
theorem numerator_correct (r c : Fin 64) : numerator r c=(data r c : GaussianInt) := by
  rw [← row_split r]
  generalize (⟨r.val/8, by omega⟩ : Fin 8)=b
  generalize (⟨r.val%8, by omega⟩ : Fin 8)=a
  fin_cases b

  · exact check00 a c
  · exact check01 a c
  · exact check02 a c
  · exact check03 a c
  · exact check04 a c
  · exact check05 a c
  · exact check06 a c
  · exact check07 a c
end SixQubit.Generated.SpectatorCubicTwirl
