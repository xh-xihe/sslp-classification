import MainTheory.CubeCompletionTransport
import MainTheory.Generated.FiniteOrbitWitnessShard210
import MainTheory.WImageNoGo51

/-!
# The generated logical-order-nine key is a no-go

This leaf identifies the sole generated key of logical order nine with paper
orbit 66.  The identification is not inferred from directory indices: the
literal source masks are checked against the two paper supports, and the
stored cube-action witness is checked against the literal generated target.
The paper WImage obstruction is then transported through that action.
-/

namespace MainTheory.OrderNineNoCompletion

open MainTheory.CubeCompletionTransport
open MainTheory.FiniteOrbitPipeline

namespace Base
abbrev input210 := MainTheory.Generated.FiniteOrbitBase.input210
abbrev key65 := MainTheory.Generated.FiniteOrbitBase.key65
end Base

/-- The actual pair of supports called orbit 66 in the paper. -/
def paper66Fibers : MainTheory.CubeAction.FiberPair 6
  | false => SixQubit.Order9.S0
  | true => SixQubit.Order9.S1

/-- The literal masks of generated input 210 encode both orbit-66 supports,
pointwise and with the paper's colour order. -/
theorem input210_fibers_eq_paper66 :
    fibersOfPair Base.input210 = paper66Fibers := by
  funext c
  cases c <;> decide

/-- The checked shard-210 cube action carries the actual paper support pair
to the actual payload of generated key 65. -/
theorem paper66_equivalent_key65 :
    MainTheory.DistanceSignature.LabeledEquivalent
      9 9 paper66Fibers 9 9 Base.key65.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input210.q Base.input210.m paper66Fibers
      Base.key65.q Base.key65.m Base.key65.fibers
  rw [← input210_fibers_eq_paper66]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard210.witness_validFor

/-- Paper orbit 66 admits no normalized distance-three completion. -/
theorem paper66_noCompletion : NoCompletion paper66Fibers := by
  apply not_completion_of_WImage_empty SixQubit.Order9.av 0 1 paper66Fibers
  · simpa [paper66Fibers] using SixQubit.Order9.S0_eq_fiber
  · simpa [paper66Fibers] using SixQubit.Order9.S1_eq_fiber
  · exact MainTheory.WImageNoGo51.WImage_orbit66_empty

/-- The no-go transported to the literal generated key payload. -/
theorem key65_noCompletion : NoCompletion Base.key65.fibers :=
  not_completion_of_fiberEquivalent paper66_noCompletion
    paper66_equivalent_key65.2.2

/-- The directory lookup at 65 really is the payload used above. -/
theorem keyAt65_eq :
    MainTheory.Generated.FiniteOrbitBase.keyAt 65 = Base.key65 := by
  decide

/-- The paper-id table records this support as orbit 66.  This metadata fact
is reported only after the support-and-action identification above. -/
theorem paperOrbitId65_eq :
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId 65 = 66 := by
  decide

theorem directoryKey65_noCompletion :
    NoCompletion
      (MainTheory.Generated.FiniteOrbitBase.keyAt 65).fibers := by
  simpa only [keyAt65_eq] using key65_noCompletion

/-- The literal generated directory has exactly one logical-order-nine key. -/
theorem key_m_eq_nine_iff (k : Fin 66) :
    (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 9 ↔ k = 65 := by
  fin_cases k <;> decide

/-- Every generated logical-order-nine key is excluded by the actual
orbit-66 obstruction, rather than by a comparison of numeric labels. -/
theorem noCompletion_of_orderNine (k : Fin 66)
    (hm : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 9) :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  have hk : k = 65 := (key_m_eq_nine_iff k).1 hm
  subst k
  exact directoryKey65_noCompletion

theorem paperOrbitId_eq_66_of_orderNine (k : Fin 66)
    (hm : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 9) :
    MainTheory.Generated.FiniteOrbitBase.paperOrbitId k = 66 := by
  have hk : k = 65 := (key_m_eq_nine_iff k).1 hm
  subst k
  exact paperOrbitId65_eq

end MainTheory.OrderNineNoCompletion
