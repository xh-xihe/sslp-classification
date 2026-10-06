import QECC.PhysicalOrderMin
import QECC.SmithBounds

namespace QECC

noncomputable section

namespace CodeProjector

variable {n K : ℕ} (C : CodeProjector n K)

/-- A reduced physical representative together with the binary Smith
certificate which bounds its exact order. -/
structure SmithBoundedPhysicalRepresentative
    (U : C.ProjectiveDiagonalGroup) (nu : ℕ) where
  representative : ReducedDiagonalRepresentative n
  preserves : C.Preserves representative.phase
  class_eq : C.projectiveClassMap ⟨representative.phase, preserves⟩ = U
  size : ℕ
  size_pos : 1 ≤ size
  size_le : size ≤ nu
  binaryMatrix : NonsingularBinaryMatrix size
  projectiveOrder_dvd : addOrderOf U ∣ representative.q
  physicalOrder_dvd_smith :
    representative.q ∣ binaryMatrix.finalSmithInvariant
  physicalOrder : orderOf (diagonalGate representative.phase) = representative.q
  physicalOrder_le_smith :
    representative.q ≤ binaryMatrix.finalSmithInvariant
  smith_le_beta : binaryMatrix.finalSmithInvariant ≤ smithBeta nu
  physicalOrder_le_beta : representative.q ≤ smithBeta nu
  minimalPhysicalOrder_le_beta : C.minimalPhysicalOrder U ≤ smithBeta nu

/-- A rational representative whose denominator is the final Smith invariant
of a positive-size binary matrix yields the complete physical-order bound. -/
theorem exists_smithBoundedPhysicalRepresentative
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0)
    {nu s : ℕ} (hspos : 1 ≤ s) (hsnu : s ≤ nu)
    (M : NonsingularBinaryMatrix s) (a : Fin n → ℤ)
    (hpres : C.Preserves
      (rationalPhase M.finalSmithInvariant a))
    (hclass : C.projectiveClassMap
      ⟨rationalPhase M.finalSmithInvariant a, hpres⟩ = U) :
    Nonempty (C.SmithBoundedPhysicalRepresentative U nu) := by
  let d := M.finalSmithInvariant
  have hd : 0 < d := M.finalSmithInvariant_pos
  have hkill : d • rationalPhase d a = 0 := rationalPhase_nsmul hd a
  obtain ⟨R, hRpres, hRclass, hmdiv, hqdiv, horder⟩ :=
    C.exists_reduced_representative_of_nsmul_eq_zero
      (rationalPhase d a) hpres U hclass hU d hd hkill
  have hqle : R.q ≤ d := Nat.le_of_dvd hd hqdiv
  have hdbeta : d ≤ smithBeta nu :=
    finalSmithInvariant_le_smithBeta hspos hsnu M
  have hqbeta : R.q ≤ smithBeta nu := hqle.trans hdbeta
  have hminbeta : C.minimalPhysicalOrder U ≤ smithBeta nu :=
    (C.minimalPhysicalOrder_le U R hRpres hRclass).trans hqbeta
  exact ⟨{
    representative := R
    preserves := hRpres
    class_eq := hRclass
    size := s
    size_pos := hspos
    size_le := hsnu
    binaryMatrix := M
    projectiveOrder_dvd := hmdiv
    physicalOrder_dvd_smith := hqdiv
    physicalOrder := horder
    physicalOrder_le_smith := hqle
    smith_le_beta := hdbeta
    physicalOrder_le_beta := hqbeta
    minimalPhysicalOrder_le_beta := hminbeta }⟩

end CodeProjector

end

end QECC
