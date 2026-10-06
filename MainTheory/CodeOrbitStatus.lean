import MainTheory.CodeOrbitKey
import MainTheory.RealizationOrbits15
import MainTheory.OrderRange
import MainTheory.OrderFiveUniqueCompletion

/-!
# The orbit statements, at the level of codes

`OrderRange.maxLogicalOrder_eq_five` and
`RealizationOrbits15.hasCompletion_iff_mem_realizationKeys` are statements
about the sixty-six *directory keys*.  The paper's Results I and II are about
*codes*.  `CodeOrbitKey.code_reaches_orbit_key` closes that distance, and this
file spends it.

The remaining step is small: a code's own fibre pair admits a completion, namely
the code, and `CubeCompletionTransport.completion_of_fiberEquivalent` carries
that along the labelled equivalence to the key.  Since the equivalence is
*labelled*, the key's `m` is the code's own.
-/

namespace MainTheory.CodeOrbitStatus

open MainTheory
open MainTheory.CubeCompletionTransport
open MainTheory.FiniteOrbitPipeline
open MainTheory.SortedForm
open MainTheory.OuterCompleteness
open MainTheory.CodeFiberBridge

variable {C : CodeSpec.ExactCode 6 2 3}

/-- **A normal form's own fibre pair is completed by the normal form**, as
data rather than as an existence statement.

`hasCompletion_codePair` used to build exactly this term and then forget it.
The forgetting is what blocked the level-(iv) chain: to carry a statement
about the orbit-36 table fibres back to the code one has to push *these*
states along the cube action, and `Nonempty` erases which states they were. -/
noncomputable def completion_codePair (S : SortedNormalForm C) :
    Completion (fibersOfPair (recordFiberPair (recordOf S))) := by
  refine { states := ![S.frame.vec 0, S.frame.vec 1]
          , supported := ?_, normalized := ?_, hasDistance := ?_ }
  · intro k s hs
    obtain ⟨x, rfl⟩ := exists_word_bitString s
    fin_cases k
    · by_contra hne
      refine hs ?_
      show wordBitString x
        ∈ fiberOfMask (recordFiberPair (recordOf S)).mask0
      exact (mem_fiberOfMask_iff _ _).2 ⟨x, support_mask0 S x hne, rfl⟩
    · by_contra hne
      refine hs ?_
      show wordBitString x
        ∈ fiberOfMask (recordFiberPair (recordOf S)).mask1
      exact (mem_fiberOfMask_iff _ _).2 ⟨x, support_mask1 S x hne, rfl⟩
  · intro k
    fin_cases k
    · simpa using S.frame.orthonormal 0 0
    · simpa using S.frame.orthonormal 1 1
  · exact MainTheory.CodeDirectoryEntry.hasDistance_pair S

@[simp] theorem completion_codePair_states (S : SortedNormalForm C) :
    (completion_codePair S).states = ![S.frame.vec 0, S.frame.vec 1] := rfl

/-- A normal form's own fibre pair is completed by the normal form. -/
theorem hasCompletion_codePair (S : SortedNormalForm C) :
    HasCompletion (fibersOfPair (recordFiberPair (recordOf S))) :=
  ⟨completion_codePair S⟩

/-- **A code occupies a key, and that key carries the code's own labels.** -/
theorem exists_key (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (S : SortedNormalForm C) (k : Fin 66),
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).q = S.q ∧
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = S.m ∧
      HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  obtain ⟨S, k, hk, _⟩ :=
    MainTheory.CodeOrbitKey.code_reaches_orbit_key C theta hpres hnt
  exact ⟨S, k, hk.1.symm, hk.2.1.symm,
    completion_of_fiberEquivalent (hasCompletion_codePair S) hk.2.2⟩

/-- **The same, keeping the cube action and the element's order.**

`exists_key` throws away the two facts that make the key say anything about
the code's own states: the cube action carrying the code's fibre pair onto the
key's, and the identification of the key's `m` with the order of whichever
diagonal symmetry one started from.  Both are already proved upstream. -/
theorem exists_key_transport (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (S : SortedNormalForm C) (k : Fin 66),
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).q = S.q ∧
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = S.m ∧
      MainTheory.CubeAction.FiberEquivalent
        (fibersOfPair (recordFiberPair (recordOf S)))
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
      (∀ v : MainTheory.ClassificationLevels.diagonalSymmetryGroup
          (MainTheory.GlobalClassificationBridge.exactCodeProjector C),
        (∀ j, Complex.exp (2 * (Real.pi : ℂ) * Complex.I
          * ((theta j : ℝ) : ℂ))
            = (((v : MainTheory.ClassificationLevels.LocalPhase 6) j : ℂ))) →
        S.m = orderOf (MainTheory.ClassificationLevels.intrinsicClass
          (MainTheory.GlobalClassificationBridge.exactCodeProjector C) v)) := by
  obtain ⟨S, k, hk, hord⟩ :=
    MainTheory.CodeOrbitKey.code_reaches_orbit_key C theta hpres hnt
  exact ⟨S, k, hk.1.symm, hk.2.1.symm, hk.2.2, hord⟩

/-- **Result I, at the level of codes.**

Every exact `((6,2,3))` code with a projectively nontrivial diagonal symmetry
has projective logical order two, three or five. -/
theorem code_logicalOrder_mem (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C, S.m = 2 ∨ S.m = 3 ∨ S.m = 5 := by
  obtain ⟨S, k, _, hm, hc⟩ := exists_key C theta hpres hnt
  refine ⟨S, ?_⟩
  rcases MainTheory.OrderRange.logicalOrder_mem k hc with h | h | h
  · exact Or.inl (by rw [← hm, h])
  · exact Or.inr (Or.inl (by rw [← hm, h]))
  · exact Or.inr (Or.inr (by rw [← hm, h]))

/-- **Result II, at the level of codes.**

Every such code lands on one of the fifteen SSLP realization orbits. -/
theorem code_in_realization_orbit (C : CodeSpec.ExactCode 6 2 3)
    (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (S : SortedNormalForm C) (k : Fin 66),
      k ∈ MainTheory.RealizationOrbits15.realizationKeys ∧
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = S.m := by
  obtain ⟨S, k, _, hm, hc⟩ := exists_key C theta hpres hnt
  exact ⟨S, k,
    (MainTheory.RealizationOrbits15.hasCompletion_iff_mem_realizationKeys k).1 hc,
    hm⟩

/-- **`M_3(6) = 5` at the level of codes**: five is attained and nothing
larger occurs. -/
theorem code_logicalOrder_le_five (C : CodeSpec.ExactCode 6 2 3)
    (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C, S.m ≤ 5 := by
  obtain ⟨S, h⟩ := code_logicalOrder_mem C theta hpres hnt
  exact ⟨S, by rcases h with h | h | h <;> omega⟩

/-- **Result IV, first claim, at the level of codes.**

Every exact `((6,2,3))` code whose diagonal symmetry has projective logical
order five occupies paper orbit `36`.  The seven other order-five moment
orbits are exact no-go cases
(`OrderFiveUniqueCompletion.paperOrbitId_eq_36_of_orderFive_completion`); what
was missing was the passage from a code to a key, which
`CodeOrbitKey.code_reaches_orbit_key` now supplies.

Together with `Orbit36LUBridge.original_projector_luEquivalent_canonical`,
which is the rigidity half, this is `thm:unique-C5-LU`. -/
theorem code_orderFive_is_orbit36 (C : CodeSpec.ExactCode 6 2 3)
    (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (S : SortedNormalForm C) (k : Fin 66),
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = S.m ∧
      (S.m = 5 →
        MainTheory.Generated.FiniteOrbitBase.paperOrbitId k = 36) := by
  obtain ⟨S, k, _, hm, hc⟩ := exists_key C theta hpres hnt
  refine ⟨S, k, hm, fun h5 => ?_⟩
  exact MainTheory.OrderFiveUniqueCompletion.paperOrbitId_eq_36_of_orderFive_completion
    k (hm.trans h5) hc

end MainTheory.CodeOrbitStatus
