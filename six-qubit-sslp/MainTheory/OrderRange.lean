import MainTheory.OrderFourNoCompletion
import MainTheory.OrderSevenNoCompletion
import MainTheory.OrderSixNoCompletion
import MainTheory.OrderEightNoCompletion
import MainTheory.OrderNineNoCompletion
import MainTheory.OrderFiveUniqueCompletion
import MainTheory.WImages
import MainTheory.Generated.FiniteOrbitWitnessShard008
import MainTheory.Generated.FiniteOrbitWitnessShard020
import MainTheory.Generated.FiniteOrbitWitnessShard118

/-!
# Which orders an exact `((6,2,3))` code can carry

Two statements about the sixty-six canonical orbits, one for each of the two
orders a diagonal logical operation has.

* **Logical order.**  `logicalOrder_mem`: a key with an exact normalized
  distance-three completion has `m ∈ {2, 3, 5}`, and `maxLogicalOrder_eq_five`
  says the largest is attained.  This is `thm:six-M3` in the paper.
* **Physical order.**  `physicalOrder_le_six` and `maxPhysicalOrder_eq_six`:
  the same statement for `q`.  The paper states only the logical half; the
  physical half is its companion, and the two are genuinely different --
  `m = 2` occurs at `q = 2, 4` and `6`, so bounding one does not bound the
  other.

Both are conditional on the directory being exhaustive, which is what
`FiniteOrbitCertificate` and the reduction chain supply, and both are one
`decide` away from the no-completion layers: orders 4, 6, 7, 8 and 9 are ruled
out key by key, and orders 2, 3 and 5 are exhibited by actual codes.

The order-4 and order-7 layers were the two that did not exist -- fifteen of
the sixty-six keys, more than all the ruled-out orders put together -- so
until now nothing prevented a code of logical order four.
-/

namespace MainTheory.OrderRange

open MainTheory.CubeAction
open MainTheory.CubeCompletionTransport
open MainTheory.FiniteOrbitPipeline

namespace Base
abbrev input008 := MainTheory.Generated.FiniteOrbitBase.input008
abbrev input020 := MainTheory.Generated.FiniteOrbitBase.input020
abbrev input118 := MainTheory.Generated.FiniteOrbitBase.input118
abbrev key06 := MainTheory.Generated.FiniteOrbitBase.key06
abbrev key09 := MainTheory.Generated.FiniteOrbitBase.key09
abbrev key45 := MainTheory.Generated.FiniteOrbitBase.key45
end Base

/-! ## Three more realized keys

`OrderFiveUniqueCompletion.key34_hasCompletion` already exhibits a code of
logical order five.  These three add logical orders two and three, and
physical orders three, four and six -- the last being the one the physical
bound is sharp at. -/

/-- The two residue fibres of paper orbit 7, written as the filters
themselves so that the completion transport needs no support lemma. -/
def paper7Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit7Real.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit7Real.av x = 1

def paper11Fibers : FiberPair 6
  | false => Finset.univ.filter fun x => SS.weight SixQubit.Orbit11Real.av x = 0
  | true => Finset.univ.filter fun x => SS.weight SixQubit.Orbit11Real.av x = 2

def paper45Fibers : FiberPair 6
  | false =>
      Finset.univ.filter fun x => SS.weight SixQubit.Orbit45Support.av x = 0
  | true =>
      Finset.univ.filter fun x => SS.weight SixQubit.Orbit45Support.av x = 3

theorem paper7_hasCompletion : HasCompletion paper7Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit7Real.av 0 1 paper7Fibers rfl rfl
    (A := MainTheory.WImages.FI 1)
  rw [MainTheory.WImages.WImage_orbit7]
  exact ⟨1, by norm_num, rfl⟩

theorem paper11_hasCompletion : HasCompletion paper11Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit11Real.av 0 2 paper11Fibers rfl
    rfl (A := MainTheory.WImages.E1A)
  rw [MainTheory.WImages.WImage_orbit11]
  rfl

theorem paper45_hasCompletion : HasCompletion paper45Fibers := by
  apply completion_of_mem_WImage SixQubit.Orbit45Support.av 0 3 paper45Fibers
    rfl rfl (A := MainTheory.WImages.FII 1)
  rw [MainTheory.WImages.WImage_orbit45]
  exact ⟨1, by norm_num, rfl⟩

theorem input008_fibers_eq_paper7 :
    fibersOfPair Base.input008 = paper7Fibers := by
  funext c
  cases c <;> decide

theorem input020_fibers_eq_paper11 :
    fibersOfPair Base.input020 = paper11Fibers := by
  funext c
  cases c <;> decide

theorem input118_fibers_eq_paper45 :
    fibersOfPair Base.input118 = paper45Fibers := by
  funext c
  cases c <;> decide

theorem paper7_equivalent_key06 :
    MainTheory.DistanceSignature.LabeledEquivalent
      3 3 paper7Fibers 3 3 Base.key06.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input008.q Base.input008.m paper7Fibers
      Base.key06.q Base.key06.m Base.key06.fibers
  rw [← input008_fibers_eq_paper7]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard008.witness_validFor

theorem paper11_equivalent_key09 :
    MainTheory.DistanceSignature.LabeledEquivalent
      4 2 paper11Fibers 4 2 Base.key09.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input020.q Base.input020.m paper11Fibers
      Base.key09.q Base.key09.m Base.key09.fibers
  rw [← input020_fibers_eq_paper11]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard020.witness_validFor

theorem paper45_equivalent_key45 :
    MainTheory.DistanceSignature.LabeledEquivalent
      6 2 paper45Fibers 6 2 Base.key45.fibers := by
  change MainTheory.DistanceSignature.LabeledEquivalent
    Base.input118.q Base.input118.m paper45Fibers
      Base.key45.q Base.key45.m Base.key45.fibers
  rw [← input118_fibers_eq_paper45]
  exact OrbitWitness.labeledEquivalent_of_validFor
    MainTheory.Generated.FiniteOrbitWitnessShard118.witness_validFor

theorem keyAt06_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 6 = Base.key06 :=
  by decide
theorem keyAt09_eq : MainTheory.Generated.FiniteOrbitBase.keyAt 9 = Base.key09 :=
  by decide
theorem keyAt45_eq :
    MainTheory.Generated.FiniteOrbitBase.keyAt 45 = Base.key45 := by decide

theorem key06_hasCompletion :
    HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 6).fibers := by
  rw [keyAt06_eq]
  exact completion_of_fiberEquivalent paper7_hasCompletion
    paper7_equivalent_key06.2.2

theorem key09_hasCompletion :
    HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 9).fibers := by
  rw [keyAt09_eq]
  exact completion_of_fiberEquivalent paper11_hasCompletion
    paper11_equivalent_key09.2.2

theorem key45_hasCompletion :
    HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt 45).fibers := by
  rw [keyAt45_eq]
  exact completion_of_fiberEquivalent paper45_hasCompletion
    paper45_equivalent_key45.2.2

/-! ## The logical order -/

/-- Every key's logical order is between two and nine. -/
theorem key_m_range (k : Fin 66) :
    2 ≤ (MainTheory.Generated.FiniteOrbitBase.keyAt k).m ∧
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m ≤ 9 := by
  revert k
  decide

/-- **No key of logical order 4, 6, 7, 8 or 9 admits a code.** -/
theorem noCompletion_of_m_not_two_three_five (k : Fin 66)
    (h2 : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m ≠ 2)
    (h3 : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m ≠ 3)
    (h5 : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m ≠ 5) :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  obtain ⟨hlo, hhi⟩ := key_m_range k
  have hcase : (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 4 ∨
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 6 ∨
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 7 ∨
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 8 ∨
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 9 := by omega
  rcases hcase with hm | hm | hm | hm | hm
  · exact MainTheory.OrderFourNoCompletion.noCompletion_of_orderFour k hm
  · exact MainTheory.OrderSixNoCompletion.noCompletion_of_orderSix k hm
  · exact MainTheory.OrderSevenNoCompletion.noCompletion_of_orderSeven k hm
  · exact MainTheory.OrderEightNoCompletion.noCompletion_of_orderEight k hm
  · exact MainTheory.OrderNineNoCompletion.noCompletion_of_orderNine k hm

/-- **The logical order of a realized orbit is two, three or five.**

This is the paper's `M_3(6)` statement, at the level of the canonical
directory: any exact normalized distance-three pair supported on one of the
sixty-six orbits forces `m ∈ {2, 3, 5}`. -/
theorem logicalOrder_mem (k : Fin 66)
    (W : HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers) :
    (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 2 ∨
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 3 ∨
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 5 := by
  by_contra h
  push_neg at h
  exact noCompletion_of_m_not_two_three_five k h.1 h.2.1 h.2.2 W

theorem logicalOrder_le_five (k : Fin 66)
    (W : HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers) :
    (MainTheory.Generated.FiniteOrbitBase.keyAt k).m ≤ 5 := by
  rcases logicalOrder_mem k W with h | h | h <;> omega

/-- **`M_3(6) = 5`.**  Five is an upper bound on the logical order and it is
attained, by the orbit-36 code. -/
theorem maxLogicalOrder_eq_five :
    (∀ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers →
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).m ≤ 5) ∧
      ∃ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 5 :=
  ⟨logicalOrder_le_five,
    ⟨34, MainTheory.OrderFiveUniqueCompletion.directoryKey34_hasCompletion,
      by decide⟩⟩

/-- Logical orders two, three and five all occur. -/
theorem logicalOrders_attained :
    (∃ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 2) ∧
      (∃ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 3) ∧
      (∃ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).m = 5) :=
  ⟨⟨9, key09_hasCompletion, by decide⟩,
    ⟨6, key06_hasCompletion, by decide⟩,
    ⟨34, MainTheory.OrderFiveUniqueCompletion.directoryKey34_hasCompletion,
      by decide⟩⟩

/-! ## The physical order

The companion statement the paper does not make.  It is not a corollary of the
logical one: logical order two occurs at physical orders two, four and six, so
`m ≤ 5` says nothing about `q`. -/

/-- Every key's physical order is between two and nine. -/
theorem key_q_range (k : Fin 66) :
    2 ≤ (MainTheory.Generated.FiniteOrbitBase.keyAt k).q ∧
      (MainTheory.Generated.FiniteOrbitBase.keyAt k).q ≤ 9 := by
  revert k
  decide

/-- Above six, the physical order determines the logical order: a key of
physical order 7, 8 or 9 has logical order 7, 4, 8 or 9, all of which are
ruled out. -/
theorem noCompletion_of_q_ge_seven (k : Fin 66)
    (hq : 7 ≤ (MainTheory.Generated.FiniteOrbitBase.keyAt k).q) :
    NoCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers := by
  refine noCompletion_of_m_not_two_three_five k ?_ ?_ ?_ <;>
    · revert hq
      revert k
      decide

/-- **The physical order of a realized orbit is at most six.** -/
theorem physicalOrder_le_six (k : Fin 66)
    (W : HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers) :
    (MainTheory.Generated.FiniteOrbitBase.keyAt k).q ≤ 6 := by
  by_contra h
  exact noCompletion_of_q_ge_seven k (by omega) W

/-- **`Q_3(6) = 6`.**  Six is an upper bound on the physical order and it is
attained, by the orbit-45 family. -/
theorem maxPhysicalOrder_eq_six :
    (∀ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers →
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).q ≤ 6) ∧
      ∃ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).q = 6 :=
  ⟨physicalOrder_le_six, ⟨45, key45_hasCompletion, by decide⟩⟩

/-- Physical orders three, four, five and six all occur; the paper's four open
orbits are the only candidates left at physical order two. -/
theorem physicalOrders_attained :
    (∃ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).q = 3) ∧
      (∃ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).q = 4) ∧
      (∃ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).q = 5) ∧
      (∃ k : Fin 66,
        HasCompletion (MainTheory.Generated.FiniteOrbitBase.keyAt k).fibers ∧
        (MainTheory.Generated.FiniteOrbitBase.keyAt k).q = 6) :=
  ⟨⟨6, key06_hasCompletion, by decide⟩,
    ⟨9, key09_hasCompletion, by decide⟩,
    ⟨34, MainTheory.OrderFiveUniqueCompletion.directoryKey34_hasCompletion,
      by decide⟩,
    ⟨45, key45_hasCompletion, by decide⟩⟩

end MainTheory.OrderRange
