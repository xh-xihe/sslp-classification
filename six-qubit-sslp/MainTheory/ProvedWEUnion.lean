import MainTheory.WImages
import MainTheory.WImageOrbit36

/-!
# `eq:proved-WE-union`

`thm:six-WE-status` lists eleven exact weight-enumerator images, and the
sentence after it collects them: their union is the `L`-interval together with
the upper `M`-segment and the isolated point `R_5^A`.  Every ingredient was
already a theorem here, but the union itself was never formed, and neither
were the three identities its proof needs --

  `E_1^A = L(1)`,  `E_2^A = L(0)`,  `E_2^A = M(1)`

-- which are what make the six singleton images disappear into the interval.
Those identities are also what the paper's own remark after the theorem is
about: distinct SSLP orbits can share one enumerator, so the `66` orbits
cannot be read as `66` enumerator classes.
-/

namespace MainTheory.ProvedWEUnion

open MainTheory
open MainTheory.WImages

/-! ## The three collapsing identities -/

/-- `E_1^A = L(1)`. -/
theorem FI_one : FI 1 = E1A := by
  funext j
  fin_cases j <;> norm_num [FI, E1A]

/-- `E_2^A = L(0)`. -/
theorem FI_zero : FI 0 = Levels.E2A := by
  funext j
  fin_cases j <;> norm_num [FI, Levels.E2A]

/-- `E_2^A = M(1)`. -/
theorem FII_one : FII 1 = Levels.E2A := by
  funext j
  fin_cases j <;> norm_num [FII, Levels.E2A]

/-! ## The two endpoints lie on the `L`-interval -/

theorem E1A_mem_FI : E1A ∈ FI '' Set.Icc (0 : ℝ) 1 :=
  ⟨1, by norm_num, FI_one⟩

theorem E2A_mem_FI : Levels.E2A ∈ FI '' Set.Icc (0 : ℝ) 1 :=
  ⟨0, by norm_num, FI_zero⟩

theorem FI_half_subset : FI '' Set.Icc (1 / 2 : ℝ) 1 ⊆ FI '' Set.Icc (0 : ℝ) 1 :=
  Set.image_mono (Set.Icc_subset_Icc (by norm_num) le_rfl)

/-! ## The union -/

/-- The eleven proved images, as one set. -/
noncomputable def provedImages : Set (Fin 7 → ℝ) :=
  Levels.WImage SixQubit.Orbit7Real.av 0 1 ∪
  Levels.WImage SixQubit.Orbit8Real.av 0 1 ∪
  Levels.WImage SixQubit.Orbit9Real.av 0 1 ∪
  Levels.WImage SixQubit.Orbit10Real.av 0 2 ∪
  Levels.WImage SixQubit.Orbit11Real.av 0 2 ∪
  Levels.WImage SixQubit.Orbit16Real.av 0 2 ∪
  Levels.WImage SixQubit.Orbit21Cert.av 0 2 ∪
  Levels.WImage SixQubit.Orbit22Real.av 0 2 ∪
  Levels.WImage SixQubit.Orbit23Real.av 0 2 ∪
  Levels.WImage SixQubit.Orbit45Support.av 0 3 ∪
  Levels.WImage SixQubit.Orbit36Transport.originalAv 0 1

/-- **`eq:proved-WE-union`.**

The union of the eleven exact images is the whole `L`-interval, the upper
`M`-segment `[2/3, 1]`, and the isolated point `R_5^A`. -/
theorem provedImages_eq :
    provedImages =
      FI '' Set.Icc (0 : ℝ) 1 ∪ FII '' Set.Icc (2 / 3 : ℝ) 1 ∪ {R5A} := by
  unfold provedImages
  rw [WImage_orbit7, WImage_orbit8, WImage_orbit9, WImage_orbit10,
    WImage_orbit11, WImage_orbit16, Levels.WImage_orbit21, WImage_orbit22,
    WImage_orbit23, WImage_orbit45, WImage_orbit36]
  apply Set.Subset.antisymm
  · refine Set.union_subset (Set.union_subset (Set.union_subset
      (Set.union_subset (Set.union_subset (Set.union_subset
        (Set.union_subset (Set.union_subset (Set.union_subset
          (Set.union_subset ?_ ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_
    · exact fun A hA => Or.inl (Or.inl hA)
    · exact fun A hA => Or.inl (Or.inl (FI_half_subset hA))
    · exact fun A hA => Or.inl (Or.inl (hA ▸ E2A_mem_FI))
    · exact fun A hA => Or.inl (Or.inl (hA ▸ E2A_mem_FI))
    · exact fun A hA => Or.inl (Or.inl (hA ▸ E1A_mem_FI))
    · exact fun A hA => Or.inl (Or.inl (hA ▸ E2A_mem_FI))
    · exact fun A hA => Or.inl (Or.inl (hA ▸ E2A_mem_FI))
    · exact fun A hA => Or.inl (Or.inl (hA ▸ E2A_mem_FI))
    · exact fun A hA => Or.inl (Or.inl (hA ▸ E1A_mem_FI))
    · exact fun A hA => Or.inl (Or.inr hA)
    · exact fun A hA => Or.inr hA
  · refine Set.union_subset (Set.union_subset ?_ ?_) ?_
    · exact fun A hA => Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
        (Or.inl (Or.inl (Or.inl (Or.inl hA)))))))))
    · exact fun A hA => Or.inl (Or.inr hA)
    · exact fun A hA => Or.inr hA

/-- The paper's remark that the `66` orbits cannot be read as `66` enumerator
classes, in its sharpest instance: five distinct orbits share the single
enumerator `E_2^A`. -/
theorem five_orbits_share_E2A :
    Levels.WImage SixQubit.Orbit9Real.av 0 1 = {Levels.E2A} ∧
      Levels.WImage SixQubit.Orbit10Real.av 0 2 = {Levels.E2A} ∧
      Levels.WImage SixQubit.Orbit16Real.av 0 2 = {Levels.E2A} ∧
      Levels.WImage SixQubit.Orbit21Cert.av 0 2 = {Levels.E2A} ∧
      Levels.WImage SixQubit.Orbit22Real.av 0 2 = {Levels.E2A} :=
  ⟨WImage_orbit9, WImage_orbit10, WImage_orbit16, Levels.WImage_orbit21,
    WImage_orbit22⟩

end MainTheory.ProvedWEUnion
