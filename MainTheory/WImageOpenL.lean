import MainTheory.ParityCircleImage
import SixQubit.Generated.OpenLFamilies.Orbit1
import SixQubit.Generated.OpenLFamilies.Orbit2
import SixQubit.Generated.OpenLFamilies.Orbit3
import SixQubit.Generated.OpenLFamilies.Orbit4

/-! # The four pointwise L([0,1]) inclusions for the open moment orbits -/

namespace MainTheory.WImageOpenL

theorem FI_subset_orbit1 : WImages.FI '' Set.Icc (0 : ℝ) 1 ⊆
    Levels.WImage SixQubit.OpenLOrbit1.angle 0 1 :=
  ParityCircleImage.FI_subset_WImage SixQubit.OpenLOrbit1.certificate

theorem FI_subset_orbit2 : WImages.FI '' Set.Icc (0 : ℝ) 1 ⊆
    Levels.WImage SixQubit.OpenLOrbit2.angle 0 1 :=
  ParityCircleImage.FI_subset_WImage SixQubit.OpenLOrbit2.certificate

theorem FI_subset_orbit3 : WImages.FI '' Set.Icc (0 : ℝ) 1 ⊆
    Levels.WImage SixQubit.OpenLOrbit3.angle 0 1 :=
  ParityCircleImage.FI_subset_WImage SixQubit.OpenLOrbit3.certificate

theorem FI_subset_orbit4 : WImages.FI '' Set.Icc (0 : ℝ) 1 ⊆
    Levels.WImage SixQubit.OpenLOrbit4.angle 0 1 :=
  ParityCircleImage.FI_subset_WImage SixQubit.OpenLOrbit4.certificate

end MainTheory.WImageOpenL
