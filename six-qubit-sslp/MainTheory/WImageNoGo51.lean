import MainTheory.WImageNoGoBridge
import SixQubit.CodeOrbit5
import SixQubit.CodeOrbit6
import SixQubit.CodeOrbit12
import SixQubit.CodeOrbit13
import SixQubit.CodeOrbit14
import SixQubit.CodeOrbit15
import SixQubit.CodeOrbit17
import SixQubit.CodeOrbit18
import SixQubit.CodeOrbit19
import SixQubit.CodeOrbit20
import SixQubit.CodeOrbit24
import SixQubit.CodeOrbit25
import SixQubit.CodeOrbit26
import SixQubit.CodeOrbit27
import SixQubit.CodeOrbit28
import SixQubit.CodeOrbit29
import SixQubit.CodeOrbit30
import SixQubit.CodeOrbit31
import SixQubit.CodeOrbit32
import SixQubit.CodeOrbit33
import SixQubit.CodeOrbit34
import SixQubit.CodeOrbit35
import SixQubit.CodeOrbit37
import SixQubit.CodeOrbit38
import SixQubit.CodeOrbit39
import SixQubit.CodeOrbit40
import SixQubit.CodeOrbit41
import SixQubit.CodeOrbit42
import SixQubit.CodeOrbit43
import SixQubit.CodeOrbit44
import SixQubit.CodeOrbit46
import SixQubit.CodeOrbit47
import SixQubit.CodeOrbit48
import SixQubit.CodeOrbit49
import SixQubit.CodeOrbit50
import SixQubit.CodeOrbit51
import SixQubit.CodeOrbit52
import SixQubit.CodeOrbit53
import SixQubit.CodeOrbit54
import SixQubit.CodeOrbit55
import SixQubit.CodeOrbit56
import SixQubit.CodeOrbit57
import SixQubit.CodeOrbit58
import SixQubit.CodeOrbit59
import SixQubit.CodeOrbit60
import SixQubit.CodeOrbit61
import SixQubit.CodeOrbit62
import SixQubit.CodeOrbit63
import SixQubit.CodeOrbit64
import SixQubit.CodeOrbit65
import SixQubit.CodeOrder9

/-!
# The 51 empty paper-facing weight-enumerator images

Every theorem below instantiates the generic support bridge with the exact
angle vector, both kernel-checked full-fibre equalities, and the final
code-level `no_code` theorem of that orbit.  The grouped theorem at the end
is a single kernel term containing all 51 semantic emptiness results.
-/

namespace MainTheory.WImageNoGo51

open MainTheory.WImageNoGoBridge

/-- Paper orbit 5 has empty weight-enumerator image. -/
theorem WImage_orbit5_empty :
    MainTheory.Levels.WImage SixQubit.Orbit5.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit5.av 0 1 SixQubit.Orbit5.S0 SixQubit.Orbit5.S1
    SixQubit.Orbit5.S0_eq_fiber SixQubit.Orbit5.S1_eq_fiber SixQubit.Orbit5.no_code

/-- Paper orbit 6 has empty weight-enumerator image. -/
theorem WImage_orbit6_empty :
    MainTheory.Levels.WImage SixQubit.Orbit6.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit6.av 0 1 SixQubit.Orbit6.S0 SixQubit.Orbit6.S1
    SixQubit.Orbit6.S0_eq_fiber SixQubit.Orbit6.S1_eq_fiber SixQubit.Orbit6.no_code

/-- Paper orbit 12 has empty weight-enumerator image. -/
theorem WImage_orbit12_empty :
    MainTheory.Levels.WImage SixQubit.Orbit12.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit12.av 0 2 SixQubit.Orbit12.S0 SixQubit.Orbit12.S1
    SixQubit.Orbit12.S0_eq_fiber SixQubit.Orbit12.S1_eq_fiber SixQubit.Orbit12.no_code

/-- Paper orbit 13 has empty weight-enumerator image. -/
theorem WImage_orbit13_empty :
    MainTheory.Levels.WImage SixQubit.Orbit13.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit13.av 0 2 SixQubit.Orbit13.S0 SixQubit.Orbit13.S1
    SixQubit.Orbit13.S0_eq_fiber SixQubit.Orbit13.S1_eq_fiber SixQubit.Orbit13.no_code

/-- Paper orbit 14 has empty weight-enumerator image. -/
theorem WImage_orbit14_empty :
    MainTheory.Levels.WImage SixQubit.Orbit14.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit14.av 0 2 SixQubit.Orbit14.S0 SixQubit.Orbit14.S1
    SixQubit.Orbit14.S0_eq_fiber SixQubit.Orbit14.S1_eq_fiber SixQubit.Orbit14.no_code

/-- Paper orbit 15 has empty weight-enumerator image. -/
theorem WImage_orbit15_empty :
    MainTheory.Levels.WImage SixQubit.Orbit15.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit15.av 0 2 SixQubit.Orbit15.S0 SixQubit.Orbit15.S1
    SixQubit.Orbit15.S0_eq_fiber SixQubit.Orbit15.S1_eq_fiber SixQubit.Orbit15.no_code

/-- Paper orbit 17 has empty weight-enumerator image. -/
theorem WImage_orbit17_empty :
    MainTheory.Levels.WImage SixQubit.Orbit17.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit17.av 0 2 SixQubit.Orbit17.S0 SixQubit.Orbit17.S1
    SixQubit.Orbit17.S0_eq_fiber SixQubit.Orbit17.S1_eq_fiber SixQubit.Orbit17.no_code

/-- Paper orbit 18 has empty weight-enumerator image. -/
theorem WImage_orbit18_empty :
    MainTheory.Levels.WImage SixQubit.Orbit18.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit18.av 0 2 SixQubit.Orbit18.S0 SixQubit.Orbit18.S1
    SixQubit.Orbit18.S0_eq_fiber SixQubit.Orbit18.S1_eq_fiber SixQubit.Orbit18.no_code

/-- Paper orbit 19 has empty weight-enumerator image. -/
theorem WImage_orbit19_empty :
    MainTheory.Levels.WImage SixQubit.Orbit19.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit19.av 0 2 SixQubit.Orbit19.S0 SixQubit.Orbit19.S1
    SixQubit.Orbit19.S0_eq_fiber SixQubit.Orbit19.S1_eq_fiber SixQubit.Orbit19.no_code

/-- Paper orbit 20 has empty weight-enumerator image. -/
theorem WImage_orbit20_empty :
    MainTheory.Levels.WImage SixQubit.Orbit20.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit20.av 0 2 SixQubit.Orbit20.S0 SixQubit.Orbit20.S1
    SixQubit.Orbit20.S0_eq_fiber SixQubit.Orbit20.S1_eq_fiber SixQubit.Orbit20.no_code

/-- Paper orbit 24 has empty weight-enumerator image. -/
theorem WImage_orbit24_empty :
    MainTheory.Levels.WImage SixQubit.Orbit24.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit24.av 0 2 SixQubit.Orbit24.S0 SixQubit.Orbit24.S1
    SixQubit.Orbit24.S0_eq_fiber SixQubit.Orbit24.S1_eq_fiber SixQubit.Orbit24.no_code

/-- Paper orbit 25 has empty weight-enumerator image. -/
theorem WImage_orbit25_empty :
    MainTheory.Levels.WImage SixQubit.Orbit25.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit25.av 0 1 SixQubit.Orbit25.S0 SixQubit.Orbit25.S1
    SixQubit.Orbit25.S0_eq_fiber SixQubit.Orbit25.S1_eq_fiber SixQubit.Orbit25.no_code

/-- Paper orbit 26 has empty weight-enumerator image. -/
theorem WImage_orbit26_empty :
    MainTheory.Levels.WImage SixQubit.Orbit26.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit26.av 0 1 SixQubit.Orbit26.S0 SixQubit.Orbit26.S1
    SixQubit.Orbit26.S0_eq_fiber SixQubit.Orbit26.S1_eq_fiber SixQubit.Orbit26.no_code

/-- Paper orbit 27 has empty weight-enumerator image. -/
theorem WImage_orbit27_empty :
    MainTheory.Levels.WImage SixQubit.Orbit27.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit27.av 0 1 SixQubit.Orbit27.S0 SixQubit.Orbit27.S1
    SixQubit.Orbit27.S0_eq_fiber SixQubit.Orbit27.S1_eq_fiber SixQubit.Orbit27.no_code

/-- Paper orbit 28 has empty weight-enumerator image. -/
theorem WImage_orbit28_empty :
    MainTheory.Levels.WImage SixQubit.Orbit28.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit28.av 0 1 SixQubit.Orbit28.S0 SixQubit.Orbit28.S1
    SixQubit.Orbit28.S0_eq_fiber SixQubit.Orbit28.S1_eq_fiber SixQubit.Orbit28.no_code

/-- Paper orbit 29 has empty weight-enumerator image. -/
theorem WImage_orbit29_empty :
    MainTheory.Levels.WImage SixQubit.Orbit29.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit29.av 0 1 SixQubit.Orbit29.S0 SixQubit.Orbit29.S1
    SixQubit.Orbit29.S0_eq_fiber SixQubit.Orbit29.S1_eq_fiber SixQubit.Orbit29.no_code

/-- Paper orbit 30 has empty weight-enumerator image. -/
theorem WImage_orbit30_empty :
    MainTheory.Levels.WImage SixQubit.Orbit30.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit30.av 0 1 SixQubit.Orbit30.S0 SixQubit.Orbit30.S1
    SixQubit.Orbit30.S0_eq_fiber SixQubit.Orbit30.S1_eq_fiber SixQubit.Orbit30.no_code

/-- Paper orbit 31 has empty weight-enumerator image. -/
theorem WImage_orbit31_empty :
    MainTheory.Levels.WImage SixQubit.Orbit31.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit31.av 0 1 SixQubit.Orbit31.S0 SixQubit.Orbit31.S1
    SixQubit.Orbit31.S0_eq_fiber SixQubit.Orbit31.S1_eq_fiber SixQubit.Orbit31.no_code

/-- Paper orbit 32 has empty weight-enumerator image. -/
theorem WImage_orbit32_empty :
    MainTheory.Levels.WImage SixQubit.Orbit32.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit32.av 0 1 SixQubit.Orbit32.S0 SixQubit.Orbit32.S1
    SixQubit.Orbit32.S0_eq_fiber SixQubit.Orbit32.S1_eq_fiber SixQubit.Orbit32.no_code

/-- Paper orbit 33 has empty weight-enumerator image. -/
theorem WImage_orbit33_empty :
    MainTheory.Levels.WImage SixQubit.Orbit33.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit33.av 0 1 SixQubit.Orbit33.S0 SixQubit.Orbit33.S1
    SixQubit.Orbit33.S0_eq_fiber SixQubit.Orbit33.S1_eq_fiber SixQubit.Orbit33.no_code

/-- Paper orbit 34 has empty weight-enumerator image. -/
theorem WImage_orbit34_empty :
    MainTheory.Levels.WImage SixQubit.Orbit34.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit34.av 0 1 SixQubit.Orbit34.S0 SixQubit.Orbit34.S1
    SixQubit.Orbit34.S0_eq_fiber SixQubit.Orbit34.S1_residue SixQubit.Orbit34.no_code

/-- Paper orbit 35 has empty weight-enumerator image. -/
theorem WImage_orbit35_empty :
    MainTheory.Levels.WImage SixQubit.Orbit35.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit35.av 0 1 SixQubit.Orbit35.S0 SixQubit.Orbit35.S1
    SixQubit.Orbit35.S0_eq_fiber SixQubit.Orbit35.S1_eq_fiber SixQubit.Orbit35.no_code

/-- Paper orbit 37 has empty weight-enumerator image. -/
theorem WImage_orbit37_empty :
    MainTheory.Levels.WImage SixQubit.Orbit37.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit37.av 0 1 SixQubit.Orbit37.S0 SixQubit.Orbit37.S1
    SixQubit.Orbit37.S0_eq_fiber SixQubit.Orbit37.S1_eq_fiber SixQubit.Orbit37.no_code

/-- Paper orbit 38 has empty weight-enumerator image. -/
theorem WImage_orbit38_empty :
    MainTheory.Levels.WImage SixQubit.Orbit38.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit38.av 0 1 SixQubit.Orbit38.S0 SixQubit.Orbit38.S1
    SixQubit.Orbit38.S0_eq_fiber SixQubit.Orbit38.S1_eq_fiber SixQubit.Orbit38.no_code

/-- Paper orbit 39 has empty weight-enumerator image. -/
theorem WImage_orbit39_empty :
    MainTheory.Levels.WImage SixQubit.Orbit39.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit39.av 0 1 SixQubit.Orbit39.S0 SixQubit.Orbit39.S1
    SixQubit.Orbit39.S0_eq_fiber SixQubit.Orbit39.S1_eq_fiber SixQubit.Orbit39.no_code

/-- Paper orbit 40 has empty weight-enumerator image. -/
theorem WImage_orbit40_empty :
    MainTheory.Levels.WImage SixQubit.Orbit40.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit40.av 0 1 SixQubit.Orbit40.S0 SixQubit.Orbit40.S1
    SixQubit.Orbit40.S0_eq_fiber SixQubit.Orbit40.S1_residue SixQubit.Orbit40.no_code

/-- Paper orbit 41 has empty weight-enumerator image. -/
theorem WImage_orbit41_empty :
    MainTheory.Levels.WImage SixQubit.Orbit41.av 0 3 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit41.av 0 3 SixQubit.Orbit41.S0 SixQubit.Orbit41.S1
    SixQubit.Orbit41.S0_eq_fiber SixQubit.Orbit41.S1_eq_fiber SixQubit.Orbit41.no_code

/-- Paper orbit 42 has empty weight-enumerator image. -/
theorem WImage_orbit42_empty :
    MainTheory.Levels.WImage SixQubit.Orbit42.av 0 3 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit42.av 0 3 SixQubit.Orbit42.S0 SixQubit.Orbit42.S1
    SixQubit.Orbit42.S0_eq_fiber SixQubit.Orbit42.S1_eq_fiber SixQubit.Orbit42.no_code

/-- Paper orbit 43 has empty weight-enumerator image. -/
theorem WImage_orbit43_empty :
    MainTheory.Levels.WImage SixQubit.Orbit43.av 0 3 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit43.av 0 3 SixQubit.Orbit43.S0 SixQubit.Orbit43.S1
    SixQubit.Orbit43.S0_eq_fiber SixQubit.Orbit43.S1_eq_fiber SixQubit.Orbit43.no_code

/-- Paper orbit 44 has empty weight-enumerator image. -/
theorem WImage_orbit44_empty :
    MainTheory.Levels.WImage SixQubit.Orbit44.av 0 3 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit44.av 0 3 SixQubit.Orbit44.S0 SixQubit.Orbit44.S1
    SixQubit.Orbit44.S0_eq_fiber SixQubit.Orbit44.S1_eq_fiber SixQubit.Orbit44.no_code

/-- Paper orbit 46 has empty weight-enumerator image. -/
theorem WImage_orbit46_empty :
    MainTheory.Levels.WImage SixQubit.Orbit46.av 0 3 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit46.av 0 3 SixQubit.Orbit46.S0 SixQubit.Orbit46.S1
    SixQubit.Orbit46.S0_eq_fiber SixQubit.Orbit46.S1_eq_fiber SixQubit.Orbit46.no_code

/-- Paper orbit 47 has empty weight-enumerator image. -/
theorem WImage_orbit47_empty :
    MainTheory.Levels.WImage SixQubit.Orbit47.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit47.av 0 2 SixQubit.Orbit47.S0 SixQubit.Orbit47.S1
    SixQubit.Orbit47.S0_eq_fiber SixQubit.Orbit47.S1_eq_fiber SixQubit.Orbit47.no_code

/-- Paper orbit 48 has empty weight-enumerator image. -/
theorem WImage_orbit48_empty :
    MainTheory.Levels.WImage SixQubit.Orbit48.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit48.av 0 2 SixQubit.Orbit48.S0 SixQubit.Orbit48.S1
    SixQubit.Orbit48.S0_eq_fiber SixQubit.Orbit48.S1_eq_fiber SixQubit.Orbit48.no_code

/-- Paper orbit 49 has empty weight-enumerator image. -/
theorem WImage_orbit49_empty :
    MainTheory.Levels.WImage SixQubit.Orbit49.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit49.av 0 2 SixQubit.Orbit49.S0 SixQubit.Orbit49.S1
    SixQubit.Orbit49.S0_eq_fiber SixQubit.Orbit49.S1_eq_fiber SixQubit.Orbit49.no_code

/-- Paper orbit 50 has empty weight-enumerator image. -/
theorem WImage_orbit50_empty :
    MainTheory.Levels.WImage SixQubit.Orbit50.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit50.av 0 2 SixQubit.Orbit50.S0 SixQubit.Orbit50.S1
    SixQubit.Orbit50.S0_eq_fiber SixQubit.Orbit50.S1_eq_fiber SixQubit.Orbit50.no_code

/-- Paper orbit 51 has empty weight-enumerator image. -/
theorem WImage_orbit51_empty :
    MainTheory.Levels.WImage SixQubit.Orbit51.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit51.av 0 2 SixQubit.Orbit51.S0 SixQubit.Orbit51.S1
    SixQubit.Orbit51.S0_eq_fiber SixQubit.Orbit51.S1_eq_fiber SixQubit.Orbit51.no_code

/-- Paper orbit 52 has empty weight-enumerator image. -/
theorem WImage_orbit52_empty :
    MainTheory.Levels.WImage SixQubit.Orbit52.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit52.av 0 2 SixQubit.Orbit52.S0 SixQubit.Orbit52.S1
    SixQubit.Orbit52.S0_eq_fiber SixQubit.Orbit52.S1_eq_fiber SixQubit.Orbit52.no_code

/-- Paper orbit 53 has empty weight-enumerator image. -/
theorem WImage_orbit53_empty :
    MainTheory.Levels.WImage SixQubit.Orbit53.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit53.av 0 1 SixQubit.Orbit53.S0 SixQubit.Orbit53.S1
    SixQubit.Orbit53.S0_eq_fiber SixQubit.Orbit53.S1_eq_fiber SixQubit.Orbit53.no_code

/-- Paper orbit 54 has empty weight-enumerator image. -/
theorem WImage_orbit54_empty :
    MainTheory.Levels.WImage SixQubit.Orbit54.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit54.av 0 1 SixQubit.Orbit54.S0 SixQubit.Orbit54.S1
    SixQubit.Orbit54.S0_eq_fiber SixQubit.Orbit54.S1_eq_fiber SixQubit.Orbit54.no_code

/-- Paper orbit 55 has empty weight-enumerator image. -/
theorem WImage_orbit55_empty :
    MainTheory.Levels.WImage SixQubit.Orbit55.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit55.av 0 1 SixQubit.Orbit55.S0 SixQubit.Orbit55.S1
    SixQubit.Orbit55.S0_eq_fiber SixQubit.Orbit55.S1_eq_fiber SixQubit.Orbit55.no_code

/-- Paper orbit 56 has empty weight-enumerator image. -/
theorem WImage_orbit56_empty :
    MainTheory.Levels.WImage SixQubit.Orbit56.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit56.av 0 1 SixQubit.Orbit56.S0 SixQubit.Orbit56.S1
    SixQubit.Orbit56.S0_eq_fiber SixQubit.Orbit56.S1_eq_fiber SixQubit.Orbit56.no_code

/-- Paper orbit 57 has empty weight-enumerator image. -/
theorem WImage_orbit57_empty :
    MainTheory.Levels.WImage SixQubit.Orbit57.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit57.av 0 1 SixQubit.Orbit57.S0 SixQubit.Orbit57.S1
    SixQubit.Orbit57.S0_eq_fiber SixQubit.Orbit57.S1_residue SixQubit.Orbit57.no_code

/-- Paper orbit 58 has empty weight-enumerator image. -/
theorem WImage_orbit58_empty :
    MainTheory.Levels.WImage SixQubit.Orbit58.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit58.av 0 1 SixQubit.Orbit58.S0 SixQubit.Orbit58.S1
    SixQubit.Orbit58.S0_eq_fiber SixQubit.Orbit58.S1_eq_fiber SixQubit.Orbit58.no_code

/-- Paper orbit 59 has empty weight-enumerator image. -/
theorem WImage_orbit59_empty :
    MainTheory.Levels.WImage SixQubit.Orbit59.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit59.av 0 1 SixQubit.Orbit59.S0 SixQubit.Orbit59.S1
    SixQubit.Orbit59.S0_eq_fiber SixQubit.Orbit59.S1_residue SixQubit.Orbit59.no_code

/-- Paper orbit 60 has empty weight-enumerator image. -/
theorem WImage_orbit60_empty :
    MainTheory.Levels.WImage SixQubit.Orbit60.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit60.av 0 1 SixQubit.Orbit60.S0 SixQubit.Orbit60.S1
    SixQubit.Orbit60.S0_eq_fiber SixQubit.Orbit60.S1_residue SixQubit.Orbit60.no_code

/-- Paper orbit 61 has empty weight-enumerator image. -/
theorem WImage_orbit61_empty :
    MainTheory.Levels.WImage SixQubit.Orbit61.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit61.av 0 1 SixQubit.Orbit61.S0 SixQubit.Orbit61.S1
    SixQubit.Orbit61.S0_eq_fiber SixQubit.Orbit61.S1_eq_fiber SixQubit.Orbit61.no_code

/-- Paper orbit 62 has empty weight-enumerator image. -/
theorem WImage_orbit62_empty :
    MainTheory.Levels.WImage SixQubit.Orbit62.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit62.av 0 2 SixQubit.Orbit62.S0 SixQubit.Orbit62.S1
    SixQubit.Orbit62.S0_eq_fiber SixQubit.Orbit62.S1_eq_fiber SixQubit.Orbit62.no_code

/-- Paper orbit 63 has empty weight-enumerator image. -/
theorem WImage_orbit63_empty :
    MainTheory.Levels.WImage SixQubit.Orbit63.av 0 2 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit63.av 0 2 SixQubit.Orbit63.S0 SixQubit.Orbit63.S1
    SixQubit.Orbit63.S0_eq_fiber SixQubit.Orbit63.S1_residue SixQubit.Orbit63.no_code

/-- Paper orbit 64 has empty weight-enumerator image. -/
theorem WImage_orbit64_empty :
    MainTheory.Levels.WImage SixQubit.Orbit64.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit64.av 0 1 SixQubit.Orbit64.S0 SixQubit.Orbit64.S1
    SixQubit.Orbit64.S0_eq_fiber SixQubit.Orbit64.S1_residue SixQubit.Orbit64.no_code

/-- Paper orbit 65 has empty weight-enumerator image. -/
theorem WImage_orbit65_empty :
    MainTheory.Levels.WImage SixQubit.Orbit65.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Orbit65.av 0 1 SixQubit.Orbit65.S0 SixQubit.Orbit65.S1
    SixQubit.Orbit65.S0_eq_fiber SixQubit.Orbit65.S1_eq_fiber SixQubit.Orbit65.no_code

/-- Paper orbit 66 has empty weight-enumerator image. -/
theorem WImage_orbit66_empty :
    MainTheory.Levels.WImage SixQubit.Order9.av 0 1 = ∅ :=
  WImage_eq_empty_of_noCode
    SixQubit.Order9.av 0 1 SixQubit.Order9.S0 SixQubit.Order9.S1
    SixQubit.Order9.S0_eq_fiber SixQubit.Order9.S1_eq_fiber SixQubit.Order9.no_code

def Q3NoGoStatement : Prop :=
  MainTheory.Levels.WImage SixQubit.Orbit5.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit6.av 0 1 = ∅

theorem q3_no_go_WImages : Q3NoGoStatement := by
  exact ⟨WImage_orbit5_empty, WImage_orbit6_empty⟩

def Q4NoGoStatement : Prop :=
  MainTheory.Levels.WImage SixQubit.Orbit12.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit13.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit14.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit15.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit17.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit18.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit19.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit20.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit24.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit25.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit26.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit27.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit28.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit29.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit30.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit31.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit32.av 0 1 = ∅

theorem q4_no_go_WImages : Q4NoGoStatement := by
  exact ⟨WImage_orbit12_empty, WImage_orbit13_empty, WImage_orbit14_empty, WImage_orbit15_empty, WImage_orbit17_empty, WImage_orbit18_empty, WImage_orbit19_empty, WImage_orbit20_empty, WImage_orbit24_empty, WImage_orbit25_empty, WImage_orbit26_empty, WImage_orbit27_empty, WImage_orbit28_empty, WImage_orbit29_empty, WImage_orbit30_empty, WImage_orbit31_empty, WImage_orbit32_empty⟩

def Q5NoGoStatement : Prop :=
  MainTheory.Levels.WImage SixQubit.Orbit33.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit34.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit35.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit37.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit38.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit39.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit40.av 0 1 = ∅

theorem q5_no_go_WImages : Q5NoGoStatement := by
  exact ⟨WImage_orbit33_empty, WImage_orbit34_empty, WImage_orbit35_empty, WImage_orbit37_empty, WImage_orbit38_empty, WImage_orbit39_empty, WImage_orbit40_empty⟩

def Q6NoGoStatement : Prop :=
  MainTheory.Levels.WImage SixQubit.Orbit41.av 0 3 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit42.av 0 3 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit43.av 0 3 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit44.av 0 3 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit46.av 0 3 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit47.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit48.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit49.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit50.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit51.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit52.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit53.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit54.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit55.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit56.av 0 1 = ∅

theorem q6_no_go_WImages : Q6NoGoStatement := by
  exact ⟨WImage_orbit41_empty, WImage_orbit42_empty, WImage_orbit43_empty, WImage_orbit44_empty, WImage_orbit46_empty, WImage_orbit47_empty, WImage_orbit48_empty, WImage_orbit49_empty, WImage_orbit50_empty, WImage_orbit51_empty, WImage_orbit52_empty, WImage_orbit53_empty, WImage_orbit54_empty, WImage_orbit55_empty, WImage_orbit56_empty⟩

def Q7NoGoStatement : Prop :=
  MainTheory.Levels.WImage SixQubit.Orbit57.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit58.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit59.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit60.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit61.av 0 1 = ∅

theorem q7_no_go_WImages : Q7NoGoStatement := by
  exact ⟨WImage_orbit57_empty, WImage_orbit58_empty, WImage_orbit59_empty, WImage_orbit60_empty, WImage_orbit61_empty⟩

def Q8NoGoStatement : Prop :=
  MainTheory.Levels.WImage SixQubit.Orbit62.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit63.av 0 2 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit64.av 0 1 = ∅ ∧
  MainTheory.Levels.WImage SixQubit.Orbit65.av 0 1 = ∅

theorem q8_no_go_WImages : Q8NoGoStatement := by
  exact ⟨WImage_orbit62_empty, WImage_orbit63_empty, WImage_orbit64_empty, WImage_orbit65_empty⟩

def Q9NoGoStatement : Prop :=
  MainTheory.Levels.WImage SixQubit.Order9.av 0 1 = ∅

theorem q9_no_go_WImages : Q9NoGoStatement := by
  exact WImage_orbit66_empty

/-- One aggregate kernel theorem containing all 51 empty-image results. -/
theorem all_51_no_go_WImages :
    Q3NoGoStatement ∧ Q4NoGoStatement ∧ Q5NoGoStatement ∧
    Q6NoGoStatement ∧ Q7NoGoStatement ∧ Q8NoGoStatement ∧
    Q9NoGoStatement := by
  exact ⟨q3_no_go_WImages, q4_no_go_WImages, q5_no_go_WImages,
    q6_no_go_WImages, q7_no_go_WImages, q8_no_go_WImages,
    q9_no_go_WImages⟩

def noGoOrbitIds : List Nat :=
  [5, 6, 12, 13, 14, 15, 17, 18, 19, 20, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 37, 38, 39, 40, 41, 42, 43, 44, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]

theorem noGoOrbitIds_length : noGoOrbitIds.length = 51 := by decide
theorem noGoOrbitIds_nodup : noGoOrbitIds.Nodup := by decide

end MainTheory.WImageNoGo51

