import QECC.GeneralPhysicalOrderBound
import QECC.DistanceThreeOrderBound

namespace QECC

noncomputable section

namespace CodeProjector

variable {n d : ℕ} (C : CodeProjector n 2)

/-- **Rank-two cutoff at distance at least two.**

Every nonzero projective diagonal logical class on a rank-two code of
distance at least two has a reduced physical representative of exact order
`q` with `addOrderOf U ∣ q` and `2 ≤ q ≤ smithBeta (n + 1)`.  The same
cutoff bounds the minimum physical order of the class. -/
theorem rankTwo_distanceTwo_physicalOrder_cutoff
    (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    ∃ (R : ReducedDiagonalRepresentative n)
      (hpres : C.Preserves R.phase),
      C.projectiveClassMap ⟨R.phase, hpres⟩ = U ∧
      addOrderOf U ∣ R.q ∧
      orderOf (diagonalGate R.phase) = R.q ∧
      2 ≤ R.q ∧
      R.q ≤ smithBeta (n + 1) ∧
      C.minimalPhysicalOrder U ≤ smithBeta (n + 1) := by
  have hdTwo : C.HasDistanceAtLeast 2 := by
    intro p hp
    exact hd p (lt_of_lt_of_le hp hd2)
  have hdetect : C.DetectsNumberOps :=
    C.detectsNumberOps_of_detectsSingleZ
      (C.detectsSingleZ_of_hasDistanceAtLeast_two hdTwo)
  obtain ⟨G⟩ := C.general_physicalOrder_bound hdetect U hU
  let R := G.bounded.representative
  let hpres : C.Preserves R.phase := G.bounded.preserves
  have hclass : C.projectiveClassMap ⟨R.phase, hpres⟩ = U := by
    exact G.bounded.class_eq
  have hqBeta : R.q ≤ smithBeta (n + 1) := by
    simpa [R] using G.physicalOrder_le_rankBeta
  have hminBeta : C.minimalPhysicalOrder U ≤ smithBeta (n + 1) := by
    simpa using G.minimalPhysicalOrder_le_rankBeta
  exact ⟨R, hpres, hclass, G.bounded.projectiveOrder_dvd,
    G.bounded.physicalOrder, R.q_ge_two, hqBeta, hminBeta⟩

/-- **Rank-two cutoff at distance at least three.**

At distance at least three, the common-affine-span argument improves the
rank-two cutoff by one variable: every nonzero projective diagonal logical
class has a reduced representative of exact order `q` with
`addOrderOf U ∣ q` and `2 ≤ q ≤ smithBeta n`.  Its minimum physical order is
bounded by the same quantity. -/
theorem rankTwo_distanceThree_physicalOrder_cutoff
    (hd : C.HasDistanceAtLeast d) (hd3 : 3 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    ∃ (R : ReducedDiagonalRepresentative n)
      (hpres : C.Preserves R.phase),
      C.projectiveClassMap ⟨R.phase, hpres⟩ = U ∧
      addOrderOf U ∣ R.q ∧
      orderOf (diagonalGate R.phase) = R.q ∧
      2 ≤ R.q ∧
      R.q ≤ smithBeta n ∧
      C.minimalPhysicalOrder U ≤ smithBeta n := by
  obtain ⟨B⟩ := C.distanceThree_physicalOrder_bound hd hd3 U hU
  exact ⟨B.representative, B.preserves, B.class_eq,
    B.projectiveOrder_dvd, B.physicalOrder, B.physicalOrder_ge_two,
    B.physicalOrder_le_beta_n, B.minimalPhysicalOrder_le_beta_n⟩

/-- The symbolic rank-two cutoff appearing in the finite-enumeration
summary: distance two uses one auxiliary logical-phase variable, while
distance at least three uses the common affine dimension bound. -/
def rankTwoPhysicalOrderCutoff (n d : ℕ) : ℕ :=
  if d = 2 then smithBeta (n + 1) else smithBeta n

/-- Piecewise form of the two abstract rank-two cutoff corollaries. -/
theorem rankTwo_physicalOrder_cutoff
    (hd : C.HasDistanceAtLeast d) (hd2 : 2 ≤ d)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    ∃ (R : ReducedDiagonalRepresentative n)
      (hpres : C.Preserves R.phase),
      C.projectiveClassMap ⟨R.phase, hpres⟩ = U ∧
      addOrderOf U ∣ R.q ∧
      orderOf (diagonalGate R.phase) = R.q ∧
      2 ≤ R.q ∧
      R.q ≤ rankTwoPhysicalOrderCutoff n d ∧
      C.minimalPhysicalOrder U ≤ rankTwoPhysicalOrderCutoff n d := by
  by_cases heq : d = 2
  · subst d
    simpa [rankTwoPhysicalOrderCutoff] using
      (C.rankTwo_distanceTwo_physicalOrder_cutoff hd (by omega) U hU)
  · have hd3 : 3 ≤ d := by omega
    simpa [rankTwoPhysicalOrderCutoff, heq] using
      (C.rankTwo_distanceThree_physicalOrder_cutoff hd hd3 U hU)

end CodeProjector

end

end QECC
