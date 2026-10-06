import MainTheory.WImages
import SixQubit.ParityCircleFamily

/-! # A certified circle family's complete closed-interval L inclusion -/

namespace MainTheory.ParityCircleImage

open SS.MacWilliams SixQubit.ParityCircleFamily

theorem FI_subset_WImage (T : Certificate) :
    WImages.FI '' Set.Icc (0 : ℝ) 1 ⊆ Levels.WImage T.angle 0 1 := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨C,S,hCS,hA⟩ := T.attain a ha.1 ha.2
  refine ⟨T.word T.c0 C S, T.word T.c1 C S, T.supported0 C S, T.supported1 C S,
    T.normalized C S hCS 0, T.normalized C S hCS 1, T.hasDistance C S hCS, ?_⟩
  intro j
  obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := hA
  change WImages.FI a j = Aco (T.state C S) j / 4
  fin_cases j <;> simp [WImages.FI,h0,h1,h2,h3,h4,h5,h6]

end MainTheory.ParityCircleImage
