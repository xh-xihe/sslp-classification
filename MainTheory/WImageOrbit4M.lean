import SixQubit.Generated.OpenMParity.Certificate
import SixQubit.OpenMImage
import MainTheory.WImageOrbit1

/-! # The full M interval is realized in orbit 4

This wrapper instantiates the polynomial semantic theorem with the actual
kernel-checked parity amplitude table and every finite KL/trace certificate.
-/

namespace MainTheory.WImageOrbit4M

open SixQubit.OpenMParity SixQubit.Orbit8Family

noncomputable section

private theorem model_correct (P : SS.PauliString 6) (hP : P.wt ≤ 3) :
    CircleZero (QuadZ.sub
      (SixQubit.ParityCircleFamily.qtrace certificate.c0 certificate.c1
        certificate.L0 certificate.L1 P) (traceModel P)) :=
  (all_rows P).2 hP

/-- Every M(t), 2/3 ≤ t ≤ 1, is attained in orbit 4's two parity fibers. -/
theorem FII_subset_WImage_orbit4 :
    WImages.FII '' Set.Icc (2/3 : ℝ) 1 ⊆ Levels.WImage angle 0 1 :=
  SixQubit.OpenMParity.Image.FII_subset_WImage certificate rfl model_correct

/-- The manuscript's full intersection inclusion, with the two actual fibers. -/
theorem FII_subset_WImage_orbit1_inter_orbit4 :
    WImages.FII '' Set.Icc (2/3 : ℝ) 1 ⊆
      Levels.WImage WImageOrbit1.orbit1Av 0 1 ∩ Levels.WImage angle 0 1 :=
  fun _ h => ⟨WImageOrbit1.FII_subset_WImage_orbit1 h, FII_subset_WImage_orbit4 h⟩

end

end MainTheory.WImageOrbit4M
