import QECC.RankTwoSSLP

namespace QECC

noncomputable section

namespace CodeProjector

/-- **Unconditional rank-two cyclicity.**  If every single-site `Z` error is
detected, the projective group of code-preserving diagonal product gates on a
two-dimensional code is cyclic.

When the group has a nonzero class, that class supplies the two
one-dimensional logical eigensectors used by the faithful phase-ratio
character.  If no such class exists, the group is trivial and hence cyclic. -/
theorem projectiveDiagonalGroup_isAddCyclic
    {n : ℕ} (C : CodeProjector n 2) (hZ : C.DetectsSingleZ) :
    IsAddCyclic C.ProjectiveDiagonalGroup := by
  classical
  by_cases hnontrivial : ∃ U : C.ProjectiveDiagonalGroup, U ≠ 0
  · obtain ⟨U, hU⟩ := hnontrivial
    exact C.projectiveDiagonalGroup_isAddCyclic_of_rankTwo hZ U hU
  · have hallzero : ∀ U : C.ProjectiveDiagonalGroup, U = 0 := by
      simpa only [not_exists, not_ne_iff] using hnontrivial
    letI : Subsingleton C.ProjectiveDiagonalGroup :=
      ⟨fun U V => (hallzero U).trans (hallzero V).symm⟩
    exact isAddCyclic_of_subsingleton

end CodeProjector

end

end QECC
