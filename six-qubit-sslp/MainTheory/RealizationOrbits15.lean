import MainTheory.DirectoryOrbitStatus
import MainTheory.OpenOrbitsRealized

/-!
# `thm:six-15-sslp-realization-orbits`

The 20260902 revision replaces the previous Result II (the `66` moment orbits,
which moved up into the reduction section) with a new statement: among the
`66` rank-compatible SSLP moment orbits, the full weight-at-most-two
Knill--Laflamme system admits an exact completion **if and only if** the orbit
is one of

  `{1, 2, 3, 4, 7, 8, 9, 10, 11, 16, 21, 22, 23, 36, 45}`,

so there are exactly fifteen realization orbits, distributed `11 : 3 : 1` over
the targeted logical orders `2 : 3 : 5`.

Both halves are now available.  The "only if" half is the fifty-one no-go
certificates, which this development has carried for a while.  The "if" half
needed the four keys the previous draft left open, and
`OpenOrbitsRealized` supplies them.

Note what is *not* claimed.  The weight-enumerator images of orbits `1`--`4`
remain undetermined (`rem:four-open-orbits`); Result III still settles eleven
images, not fifteen.  Only nonemptiness of `K_r` is established here.
-/

namespace MainTheory.RealizationOrbits15

open MainTheory
open MainTheory.CubeCompletionTransport
open MainTheory.DirectoryOrbitStatus
open MainTheory.Generated.FiniteOrbitBase

/-- The fifteen realization keys: the eleven whose weight-enumerator images
were already exact, together with the four that were open. -/
def realizationKeys : List (Fin 66) := realizedKeys ++ openKeys

theorem realizationKeys_length : realizationKeys.length = 15 := by decide

theorem realizationKeys_nodup : realizationKeys.Nodup := by decide

/-- The fifteen keys are the paper's fifteen orbit numbers,
`six:eq:15-sslp-realization-orbits`. -/
theorem realizationKeys_paperIds :
    (realizationKeys.map paperOrbitId).toFinset =
      ({1, 2, 3, 4, 7, 8, 9, 10, 11, 16, 21, 22, 23, 36, 45} : Finset ℕ) := by
  decide

/-- The complement of the fifteen is exactly the fifty-one no-go list. -/
theorem not_mem_realizationKeys_iff (k : Fin 66) :
    k ∉ realizationKeys ↔ k ∈ noGoKeys := by
  revert k
  decide

/-- **Every one of the fifteen admits an exact completion.** -/
theorem hasCompletion_of_mem_realizationKeys (k : Fin 66)
    (h : k ∈ realizationKeys) : HasCompletion (keyAt k).fibers := by
  rcases List.mem_append.1 h with hr | ho
  · exact hasCompletion_of_mem_realizedKeys k hr
  · have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
      revert ho
      revert k
      decide
    rcases this with rfl | rfl | rfl | rfl
    · exact MainTheory.OpenOrbitsRealized.key00_hasCompletion
    · exact MainTheory.OpenOrbitsRealized.key01_hasCompletion
    · exact MainTheory.OpenOrbitsRealized.key02_hasCompletion
    · exact MainTheory.OpenOrbitsRealized.key03_hasCompletion

/-- **`thm:six-15-sslp-realization-orbits`, both halves.**

An orbit key admits an exact normalized distance-three completion exactly when
it is one of the fifteen. -/
theorem hasCompletion_iff_mem_realizationKeys (k : Fin 66) :
    HasCompletion (keyAt k).fibers ↔ k ∈ realizationKeys := by
  constructor
  · intro hc
    by_contra hk
    exact noCompletion_of_mem_noGoKeys k ((not_mem_realizationKeys_iff k).1 hk) hc
  · exact hasCompletion_of_mem_realizationKeys k

open scoped Classical in
/-- **Exactly fifteen orbits are realized.** -/
theorem card_realization_orbits :
    (Finset.univ.filter fun k : Fin 66 => HasCompletion (keyAt k).fibers).card
      = 15 := by
  have h : (Finset.univ.filter fun k : Fin 66 =>
      HasCompletion (keyAt k).fibers)
      = (Finset.univ.filter fun k : Fin 66 => k ∈ realizationKeys) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hasCompletion_iff_mem_realizationKeys k
  rw [h]
  decide

/-- **The distribution by targeted logical order**, `11 : 3 : 1` over
`m = 2, 3, 5`. -/
theorem realizationKeys_orderDistribution :
    (realizationKeys.filter fun k => (keyAt k).m = 2).length = 11 ∧
      (realizationKeys.filter fun k => (keyAt k).m = 3).length = 3 ∧
      (realizationKeys.filter fun k => (keyAt k).m = 5).length = 1 := by
  decide

/-- Every realization key has one of the three admissible logical orders, so
the distribution above accounts for all fifteen. -/
theorem realizationKeys_m_mem (k : Fin 66) (h : k ∈ realizationKeys) :
    (keyAt k).m = 2 ∨ (keyAt k).m = 3 ∨ (keyAt k).m = 5 := by
  revert h
  revert k
  decide

/-! ## The census, with no open column -/

/-- **The sixty-six keys split into fifty-one no-gos and fifteen
realizations, with nothing left over.** This replaces
`DirectoryOrbitStatus.settled_or_open`, whose third disjunct was the four keys
now discharged. -/
theorem settled (k : Fin 66) :
    NoCompletion (keyAt k).fibers ∨ HasCompletion (keyAt k).fibers := by
  by_cases h : k ∈ realizationKeys
  · exact Or.inr (hasCompletion_of_mem_realizationKeys k h)
  · exact Or.inl
      (noCompletion_of_mem_noGoKeys k ((not_mem_realizationKeys_iff k).1 h))

end MainTheory.RealizationOrbits15
