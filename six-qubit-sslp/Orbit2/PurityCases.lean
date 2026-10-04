import Orbit2.PurityCases.Case000
import Orbit2.PurityCases.Case001
import Orbit2.PurityCases.Case002
import Orbit2.PurityCases.Case003
import Orbit2.PurityCases.Case004
import Orbit2.PurityCases.Case005
import Orbit2.PurityCases.Case006
import Orbit2.PurityCases.Case007
import Orbit2.PurityCases.Case008
import Orbit2.PurityCases.Case009
import Orbit2.PurityCases.Case010
import Orbit2.PurityCases.Case011
import Orbit2.PurityCases.Case012
import Orbit2.PurityCases.Case013
import Orbit2.PurityCases.Case014
import Orbit2.PurityCases.Case015
import Orbit2.PurityCases.Case016
import Orbit2.PurityCases.Case017
import Orbit2.PurityCases.Case018
import Orbit2.PurityCases.Case019
import Orbit2.PurityCases.Case020
import Orbit2.PurityCases.Case021
import Orbit2.PurityCases.Case022
import Orbit2.PurityCases.Case023
import Orbit2.PurityCases.Case024
import Orbit2.PurityCases.Case025
import Orbit2.PurityCases.Case026
import Orbit2.PurityCases.Case027
import Orbit2.PurityCases.Case028
import Orbit2.PurityCases.Case029
import Orbit2.PurityCases.Case030
import Orbit2.PurityCases.Case031
import Orbit2.PurityCases.Case032
import Orbit2.PurityCases.Case033
import Orbit2.PurityCases.Case034
import Orbit2.PurityCases.Case035
import Orbit2.PurityCases.Case036
import Orbit2.PurityCases.Case037
import Orbit2.PurityCases.Case038
import Orbit2.PurityCases.Case039
import Orbit2.PurityCases.Case040
import Orbit2.PurityCases.Case041
import Orbit2.PurityCases.Case042
import Orbit2.PurityCases.Case043
import Orbit2.PurityCases.Case044
import Orbit2.PurityCases.Case045
import Orbit2.PurityCases.Case046
import Orbit2.PurityCases.Case047
import Orbit2.PurityCases.Case048
import Orbit2.PurityCases.Case049
import Orbit2.PurityCases.Case050
import Orbit2.PurityCases.Case051
import Orbit2.PurityCases.Case052
import Orbit2.PurityCases.Case053
import Orbit2.PurityCases.Case054
import Orbit2.PurityCases.Case055
import Orbit2.PurityCases.Case056
import Orbit2.PurityCases.Case057
import Orbit2.PurityCases.Case058
import Orbit2.PurityCases.Case059
import Orbit2.PurityCases.Case060
import Orbit2.PurityCases.Case061
import Orbit2.PurityCases.Case062
import Orbit2.PurityCases.Case063
namespace Orbit2.PurityReduction
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem packed_identity (r b c : Fin 4) (a : Label 4) :
    let p := packed r b c a
    ¬ (forbidden p ∨ forbidden (partner p)) →
    purityCoefficient p + purityCoefficient (partner p) =
      -4 * (targetCoefficient p + targetCoefficient (partner p)) := by
  fin_cases r <;> fin_cases b <;> fin_cases c
  · exact Case000.checked a
  · exact Case001.checked a
  · exact Case002.checked a
  · exact Case003.checked a
  · exact Case004.checked a
  · exact Case005.checked a
  · exact Case006.checked a
  · exact Case007.checked a
  · exact Case008.checked a
  · exact Case009.checked a
  · exact Case010.checked a
  · exact Case011.checked a
  · exact Case012.checked a
  · exact Case013.checked a
  · exact Case014.checked a
  · exact Case015.checked a
  · exact Case016.checked a
  · exact Case017.checked a
  · exact Case018.checked a
  · exact Case019.checked a
  · exact Case020.checked a
  · exact Case021.checked a
  · exact Case022.checked a
  · exact Case023.checked a
  · exact Case024.checked a
  · exact Case025.checked a
  · exact Case026.checked a
  · exact Case027.checked a
  · exact Case028.checked a
  · exact Case029.checked a
  · exact Case030.checked a
  · exact Case031.checked a
  · exact Case032.checked a
  · exact Case033.checked a
  · exact Case034.checked a
  · exact Case035.checked a
  · exact Case036.checked a
  · exact Case037.checked a
  · exact Case038.checked a
  · exact Case039.checked a
  · exact Case040.checked a
  · exact Case041.checked a
  · exact Case042.checked a
  · exact Case043.checked a
  · exact Case044.checked a
  · exact Case045.checked a
  · exact Case046.checked a
  · exact Case047.checked a
  · exact Case048.checked a
  · exact Case049.checked a
  · exact Case050.checked a
  · exact Case051.checked a
  · exact Case052.checked a
  · exact Case053.checked a
  · exact Case054.checked a
  · exact Case055.checked a
  · exact Case056.checked a
  · exact Case057.checked a
  · exact Case058.checked a
  · exact Case059.checked a
  · exact Case060.checked a
  · exact Case061.checked a
  · exact Case062.checked a
  · exact Case063.checked a
end Orbit2.PurityReduction
