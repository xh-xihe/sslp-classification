import MainTheory.CubeCompletionTransport
import MainTheory.OrderFivePaperIdentification
import MainTheory.WImageNoGo51
import MainTheory.WImageOrbit36

/-!
# The unique completable order-five generated key

This is the directory-to-paper exclusion leaf required by the global
six-qubit argument.  It is deliberately stated at the exact point currently
reached by the generated classification: an actual generated `keyAt k` whose
literal fibre pair admits a normalized distance-three completion.

The proof uses the kernel identifications in
`OrderFivePaperIdentification`, transports the seven paper no-go results
through their stored cube actions, and transports the exhibited orbit-36 code
in the positive direction.  It does not assume that generated key index equals
paper orbit id.
-/

namespace MainTheory.OrderFiveUniqueCompletion

open MainTheory.CubeAction
open MainTheory.CubeCompletionTransport
open MainTheory.OrderFivePaperIdentification

/-! ## Seven paper no-go supports and the one realized support -/

theorem paper33_noCompletion : NoCompletion paper33Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit33.av 0 1
    paper33Fibers
  · simpa [paper33Fibers] using SixQubit.Orbit33.S0_eq_fiber
  · simpa [paper33Fibers] using SixQubit.Orbit33.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit33_empty

theorem paper34_noCompletion : NoCompletion paper34Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit34.av 0 1
    paper34Fibers
  · simpa [paper34Fibers] using SixQubit.Orbit34.S0_eq_fiber
  · simpa [paper34Fibers] using SixQubit.Orbit34.S1_residue
  · exact MainTheory.WImageNoGo51.WImage_orbit34_empty

theorem paper35_noCompletion : NoCompletion paper35Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit35.av 0 1
    paper35Fibers
  · simpa [paper35Fibers] using SixQubit.Orbit35.S0_eq_fiber
  · simpa [paper35Fibers] using SixQubit.Orbit35.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit35_empty

theorem paper37_noCompletion : NoCompletion paper37Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit37.av 0 1
    paper37Fibers
  · simpa [paper37Fibers] using SixQubit.Orbit37.S0_eq_fiber
  · simpa [paper37Fibers] using SixQubit.Orbit37.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit37_empty

theorem paper38_noCompletion : NoCompletion paper38Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit38.av 0 1
    paper38Fibers
  · simpa [paper38Fibers] using SixQubit.Orbit38.S0_eq_fiber
  · simpa [paper38Fibers] using SixQubit.Orbit38.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit38_empty

theorem paper39_noCompletion : NoCompletion paper39Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit39.av 0 1
    paper39Fibers
  · simpa [paper39Fibers] using SixQubit.Orbit39.S0_eq_fiber
  · simpa [paper39Fibers] using SixQubit.Orbit39.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit39_empty

theorem paper40_noCompletion : NoCompletion paper40Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Orbit40.av 0 1
    paper40Fibers
  · simpa [paper40Fibers] using SixQubit.Orbit40.S0_eq_fiber
  · simpa [paper40Fibers] using SixQubit.Orbit40.S1_residue
  · exact MainTheory.WImageNoGo51.WImage_orbit40_empty

theorem paper36_hasCompletion : HasCompletion paper36Fibers := by
  have hR : MainTheory.WImages.R5A ∈
      MainTheory.Levels.WImage
        SixQubit.Orbit36Transport.originalAv 0 1 := by
    rw [MainTheory.WImages.WImage_orbit36]
    simp
  apply completion_of_mem_WImage
    SixQubit.Orbit36Transport.originalAv 0 1 paper36Fibers
  · rfl
  · rfl
  · exact hR

/-! ## Transport to the eight actual generated keys -/

theorem key32_noCompletion :
    NoCompletion MainTheory.Generated.FiniteOrbitBase.key32.fibers :=
  not_completion_of_fiberEquivalent paper34_noCompletion
    paper34_equivalent_key32.2.2

theorem key33_noCompletion :
    NoCompletion MainTheory.Generated.FiniteOrbitBase.key33.fibers :=
  not_completion_of_fiberEquivalent paper39_noCompletion
    paper39_equivalent_key33.2.2

theorem key34_hasCompletion :
    HasCompletion MainTheory.Generated.FiniteOrbitBase.key34.fibers :=
  completion_of_fiberEquivalent paper36_hasCompletion
    paper36_equivalent_key34.2.2

theorem key35_noCompletion :
    NoCompletion MainTheory.Generated.FiniteOrbitBase.key35.fibers :=
  not_completion_of_fiberEquivalent paper40_noCompletion
    paper40_equivalent_key35.2.2

theorem key36_noCompletion :
    NoCompletion MainTheory.Generated.FiniteOrbitBase.key36.fibers :=
  not_completion_of_fiberEquivalent paper38_noCompletion
    paper38_equivalent_key36.2.2

theorem key37_noCompletion :
    NoCompletion MainTheory.Generated.FiniteOrbitBase.key37.fibers :=
  not_completion_of_fiberEquivalent paper33_noCompletion
    paper33_equivalent_key37.2.2

theorem key38_noCompletion :
    NoCompletion MainTheory.Generated.FiniteOrbitBase.key38.fibers :=
  not_completion_of_fiberEquivalent paper35_noCompletion
    paper35_equivalent_key38.2.2

theorem key39_noCompletion :
    NoCompletion MainTheory.Generated.FiniteOrbitBase.key39.fibers :=
  not_completion_of_fiberEquivalent paper37_noCompletion
    paper37_equivalent_key39.2.2

theorem directoryKey32_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 32).fibers := by
  simpa only [orderFive_key_payloads.1] using key32_noCompletion

theorem directoryKey33_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 33).fibers := by
  simpa only [orderFive_key_payloads.2.1] using key33_noCompletion

theorem directoryKey34_hasCompletion :
    HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 34).fibers := by
  simpa only [orderFive_key_payloads.2.2.1] using key34_hasCompletion

theorem directoryKey35_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 35).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.1] using key35_noCompletion

theorem directoryKey36_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 36).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.2.1] using key36_noCompletion

theorem directoryKey37_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 37).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.2.2.1] using key37_noCompletion

theorem directoryKey38_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 38).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.2.2.2.1] using key38_noCompletion

theorem directoryKey39_noCompletion :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 39).fibers := by
  simpa only [orderFive_key_payloads.2.2.2.2.2.2.2] using key39_noCompletion

/-! ## Unique completable logical-order-five key -/

/-- The actual generated keys with logical order five are exactly indices
32 through 39.  This is checked from the literal `keyAt` payloads. -/
theorem key_m_eq_five_iff (k : Fin 66) :
    (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 5 ↔
      k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35 ∨
      k = 36 ∨ k = 37 ∨ k = 38 ∨ k = 39 := by
  fin_cases k <;> decide

/-- Among all eight generated logical-order-five keys, the only one admitting
an actual normalized distance-three completion is key 34. -/
theorem eq_key34_of_orderFive_completion (k : Fin 66)
    (hm : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 5)
    (W : HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers) :
    k = 34 := by
  rcases (key_m_eq_five_iff k).1 hm with
      h | h | h | h | h | h | h | h
  · subst k
    exact (directoryKey32_noCompletion W).elim
  · subst k
    exact (directoryKey33_noCompletion W).elim
  · exact h
  · subst k
    exact (directoryKey35_noCompletion W).elim
  · subst k
    exact (directoryKey36_noCompletion W).elim
  · subst k
    exact (directoryKey37_noCompletion W).elim
  · subst k
    exact (directoryKey38_noCompletion W).elim
  · subst k
    exact (directoryKey39_noCompletion W).elim

/-- Paper-facing form: a completable logical-order-five generated key has the
actual paper orbit id 36. -/
theorem paperOrbitId_eq_36_of_orderFive_completion (k : Fin 66)
    (hm : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 5)
    (W : HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers) :
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId k = 36 := by
  have hk : k = 34 := eq_key34_of_orderFive_completion k hm W
  subst k
  exact orderFive_paper_ids.2.2.1

end MainTheory.OrderFiveUniqueCompletion
