import MainTheory.Levels
import SixQubit.Orbit36Certified

/-!
# The paper-facing weight-enumerator image of orbit 36

`SixQubit.Orbit36Certified` already proves both rigidity and attainment for
the exact representative printed in the table.  This leaf supplies the
missing level-(iii) wrapper in the normalization used by `main.tex`.
-/

namespace MainTheory.WImages

open SS.MacWilliams

/-- The normalized orbit-36 enumerator `\mathcal R_5^A` from `main.tex`. -/
noncomputable def R5A : Fin 7 → ℝ :=
  ![1, 0, 21 / 25, 0, 291 / 25, 384 / 25, 79 / 25]

set_option maxRecDepth 20000 in
/-- **Orbit 36's paper-normalized weight-enumerator image is a singleton.**

The forward inclusion is the enumerator component of the full rigidity
theorem.  The reverse inclusion uses its separately certified attainment
witness, so the singleton statement is not vacuous. -/
theorem WImage_orbit36 :
    Levels.WImage SixQubit.Orbit36Transport.originalAv 0 1 = {R5A} := by
  classical
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    have hc' : ∀ x, x ∉ SixQubit.Orbit36Transport.originalS0 → c x = 0 := by
      intro x hx
      apply hc x
      simpa [SixQubit.Orbit36Transport.originalS0] using hx
    have hd' : ∀ y, y ∉ SixQubit.Orbit36Transport.originalS1 → d y = 0 := by
      intro y hy
      apply hd y
      simpa [SixQubit.Orbit36Transport.originalS1] using hy
    obtain ⟨_, _, _, hEnum, _⟩ :=
      SixQubit.Orbit36Certified.table_representative_rigid
        c d hc' hd' hnc hnd hdist
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hEnum
    funext j
    fin_cases j <;>
      simp [R5A, hA, h0, h1, h2, h3, h4, h5, h6] <;>
      norm_num
  · intro hA
    obtain ⟨c, d, hc, hd, hnc, hnd, hdist, hEnum, _⟩ :=
      SixQubit.Orbit36Certified.table_representative_attained
    refine ⟨c, d, ?_, ?_, hnc, hnd, hdist, fun j => ?_⟩
    · intro x hx
      apply hc x
      simpa [SixQubit.Orbit36Transport.originalS0] using hx
    · intro y hy
      apply hd y
      simpa [SixQubit.Orbit36Transport.originalS1] using hy
    · have hAE : A = R5A := hA
      subst hAE
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hEnum
      fin_cases j <;>
        simp [R5A, h0, h1, h2, h3, h4, h5, h6] <;>
        norm_num

end MainTheory.WImages
