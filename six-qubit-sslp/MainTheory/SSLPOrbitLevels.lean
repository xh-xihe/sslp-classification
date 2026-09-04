import MainTheory.RealizationOrbits15

/-!
# `def:six-sslp-orbits` and level (ii) of `def:six-classification-levels`

The 20260902 revision splits what the previous draft called an SSLP orbit into
two notions, and makes the second one a classification level in its own right:

* an **SSLP moment orbit** is an orbit of the labelled full-fibre data
  `(q, m; S_0, S_{q/m})` under Boolean-cube isometries and colour interchange
  -- the intermediate object the subset-sum and moment-LP stages produce, of
  which there are `66`;
* an **SSLP realization orbit** is a moment orbit `r` whose set `K_r` of exact
  weight-at-most-two Knill--Laflamme completions is nonempty
  (`eq:Kr-definition`), of which there are `15`.

Both were previously unnamed here.  `ClassificationLevels.SSLPMomentDatum`
models the *20260822* level (ii) -- the moment-orbit level -- and has no users;
the realization-orbit notion had no Lean object at all.  This file names both
against the objects the development actually proves things about, so that
level (ii) of `def:six-classification-levels` has a counterpart rather than a
description.

`K_r` needs no new definition: `CubeCompletionTransport.Completion F` is by
construction an ordered normalized pair supported on `F` with the genuine
`SS.HasDistance _ 3`, which is exactly a member of `K_r`.

What this file does **not** supply is the active-rank data that the
20260902 `def:six-sslp-orbits` adds to the moment datum.  The rank
certificates exist (`FiniteRankPipeline.RankRow`) and their content is used
(`CodeRankFilter`), but nothing attaches them to an orbit datum, so a reader
comparing the definition clause by clause will find that clause represented
only by the filter that consumes it.
-/

namespace MainTheory.SSLPOrbitLevels

open MainTheory
open MainTheory.CubeCompletionTransport
open MainTheory.Generated.FiniteOrbitBase

/-! ## The moment orbits -/

/-- An **SSLP moment orbit**: an index of the classified orbit directory.
`Generated.FiniteOrbitCertificate.hasExactlyClasses` is what makes this the
right index type -- every rank-compatible input is covered by one of these,
and none of them is a ghost. -/
abbrev MomentOrbit : Type := Fin 66

theorem card_momentOrbit : Fintype.card MomentOrbit = 66 := by decide

/-! ## `K_r` and the realization orbits -/

/-- **`K_r`** of `eq:Kr-definition`: the exact weight-at-most-two
Knill--Laflamme completions supported on the moment orbit's two fibres. -/
abbrev KSet (r : MomentOrbit) : Type := Completion (keyAt r).fibers

/-- **An SSLP realization orbit** is a moment orbit with `K_r` nonempty. -/
def IsRealizationOrbit (r : MomentOrbit) : Prop := Nonempty (KSet r)

/-- The definition is the development's own `HasCompletion`, unfolded. -/
theorem isRealizationOrbit_iff (r : MomentOrbit) :
    IsRealizationOrbit r ↔ HasCompletion (keyAt r).fibers := Iff.rfl

/-- Level (ii) of `def:six-classification-levels`, as a type. -/
abbrev RealizationOrbit : Type := {r : MomentOrbit // IsRealizationOrbit r}

open scoped Classical in
/-- **The realization-orbit level has exactly fifteen members.**

This is the definitional reading of `thm:six-15-sslp-realization-orbits`: the
`66` moment orbits are the candidates, and only those with `K_r` nonempty
belong to level (ii). -/
theorem card_realizationOrbit :
    Nat.card RealizationOrbit = 15 := by
  have h : Nat.card RealizationOrbit
      = (Finset.univ.filter fun r : Fin 66 =>
          HasCompletion (keyAt r).fibers).card := by
    rw [Nat.card_eq_fintype_card (α := RealizationOrbit)]
    simpa [RealizationOrbit, IsRealizationOrbit, isRealizationOrbit_iff]
      using Fintype.card_subtype (p := fun r : Fin 66 => IsRealizationOrbit r)
  rw [h]
  exact MainTheory.RealizationOrbits15.card_realization_orbits

/-- Membership in level (ii) is decided by the fifteen keys. -/
theorem isRealizationOrbit_iff_mem (r : MomentOrbit) :
    IsRealizationOrbit r ↔
      r ∈ MainTheory.RealizationOrbits15.realizationKeys :=
  MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys r

/-- Every moment orbit is either a realization orbit or has empty `K_r`; the
20260822 draft's third column, the four undecided keys, is gone. -/
theorem realization_or_empty (r : MomentOrbit) :
    IsRealizationOrbit r ∨ IsEmpty (KSet r) := by
  rcases MainTheory.RealizationOrbits15.settled r with h | h
  · exact Or.inr (not_nonempty_iff.1 h)
  · exact Or.inl h

end MainTheory.SSLPOrbitLevels
