import MainTheory.Generated.Orbit31CrossRows.Flip1
import MainTheory.Generated.Orbit31CrossRows.Flip2
import MainTheory.Generated.Orbit31CrossRows.Flip3
import MainTheory.Generated.Orbit31CrossRows.Flip14
import MainTheory.Generated.Orbit31CrossRows.Flip15
import MainTheory.Generated.Orbit31CrossRows.Flip16
import MainTheory.Generated.Orbit31CrossRows.Flip24
import MainTheory.Generated.Orbit31CrossRows.Flip25
import MainTheory.Generated.Orbit31CrossRows.Flip26
import MainTheory.Generated.Orbit31CrossRows.Flip34
import MainTheory.Generated.Orbit31CrossRows.Flip35
import MainTheory.Generated.Orbit31CrossRows.Flip36

/-! Collect the actual nonempty cross-flip row systems in the SI gauge. -/
namespace MainTheory.Orbit31CrossRows
open MainTheory.Generated.Orbit31CrossRows

theorem weight_one_ranks :
    Flip1.W.rank = 5 ∧ Flip2.W.rank = 5 ∧ Flip3.W.rank = 5 :=
  ⟨Flip1.rank,Flip2.rank,Flip3.rank⟩

theorem weight_two_ranks :
    Flip14.W.rank = 2 ∧ Flip15.W.rank = 2 ∧ Flip16.W.rank = 2 ∧
    Flip24.W.rank = 2 ∧ Flip25.W.rank = 2 ∧ Flip26.W.rank = 2 ∧
    Flip34.W.rank = 2 ∧ Flip35.W.rank = 2 ∧ Flip36.W.rank = 2 :=
  ⟨Flip14.rank,Flip15.rank,Flip16.rank,Flip24.rank,Flip25.rank,Flip26.rank,
    Flip34.rank,Flip35.rank,Flip36.rank⟩

end MainTheory.Orbit31CrossRows
