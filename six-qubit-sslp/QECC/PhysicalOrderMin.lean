import QECC.FirstTheorem

namespace QECC

noncomputable section

namespace CodeProjector

variable {n K : ℕ} (C : CodeProjector n K)

/-- The natural numbers which occur as exact physical orders of reduced
diagonal representatives of a fixed projective logical class. -/
def physicalRepresentativeOrders (U : C.ProjectiveDiagonalGroup) : Set ℕ :=
  {q | ∃ (R : ReducedDiagonalRepresentative n)
      (hpres : C.Preserves R.phase),
      C.projectiveClassMap ⟨R.phase, hpres⟩ = U ∧ R.q = q}

/-- The least exact physical order among reduced diagonal representatives of
a projective logical class.  For a nonzero class under the detection
hypothesis, existence is supplied by the reduced-representative theorem. -/
def minimalPhysicalOrder (U : C.ProjectiveDiagonalGroup) : ℕ :=
  sInf (C.physicalRepresentativeOrders U)

theorem mem_physicalRepresentativeOrders
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (hclass : C.projectiveClassMap ⟨R.phase, hpres⟩ = U) :
    R.q ∈ C.physicalRepresentativeOrders U :=
  ⟨R, hpres, hclass, rfl⟩

theorem physicalRepresentativeOrders_nonempty
    (hdetect : C.DetectsNumberOps)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    (C.physicalRepresentativeOrders U).Nonempty := by
  obtain ⟨R, hpres, hclass, _hgcd, _hphysical, _hdvd⟩ :=
    C.exists_reduced_representative hdetect U hU
  exact ⟨R.q, C.mem_physicalRepresentativeOrders U R hpres hclass⟩

theorem minimalPhysicalOrder_mem
    (hdetect : C.DetectsNumberOps)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    C.minimalPhysicalOrder U ∈ C.physicalRepresentativeOrders U :=
  Nat.sInf_mem (C.physicalRepresentativeOrders_nonempty hdetect U hU)

theorem minimalPhysicalOrder_le
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (hclass : C.projectiveClassMap ⟨R.phase, hpres⟩ = U) :
    C.minimalPhysicalOrder U ≤ R.q :=
  Nat.sInf_le (C.mem_physicalRepresentativeOrders U R hpres hclass)

theorem minimalPhysicalOrder_ge_two
    (hdetect : C.DetectsNumberOps)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    2 ≤ C.minimalPhysicalOrder U := by
  obtain ⟨R, _hpres, _hclass, hq⟩ :=
    C.minimalPhysicalOrder_mem hdetect U hU
  simpa [← hq] using R.q_ge_two

theorem projectiveOrder_dvd_of_mem_physicalRepresentativeOrders
    (U : C.ProjectiveDiagonalGroup) {q : ℕ}
    (hq : q ∈ C.physicalRepresentativeOrders U) :
    addOrderOf U ∣ q := by
  obtain ⟨R, hpres, hclass, rfl⟩ := hq
  let rep : C.preservingPhases := ⟨R.phase, hpres⟩
  have hdvd := addOrderOf_map_dvd C.projectiveClassMap rep
  have hrepOrder : addOrderOf rep = R.q := by
    have hinj := addOrderOf_injective C.preservingPhases.subtype
      (AddSubgroup.subtype_injective C.preservingPhases) rep
    change addOrderOf R.phase = addOrderOf rep at hinj
    rw [R.addOrderOf_phase] at hinj
    exact hinj.symm
  rw [hclass, hrepOrder] at hdvd
  exact hdvd

theorem projectiveOrder_dvd_minimalPhysicalOrder
    (hdetect : C.DetectsNumberOps)
    (U : C.ProjectiveDiagonalGroup) (hU : U ≠ 0) :
    addOrderOf U ∣ C.minimalPhysicalOrder U :=
  C.projectiveOrder_dvd_of_mem_physicalRepresentativeOrders U
    (C.minimalPhysicalOrder_mem hdetect U hU)

/-- A nonzero projective class represented by a phase vector killed by a
positive integer has a reduced representative whose exact physical order
divides that integer.  This is the final reduction step used by the
denominator bounds in Section III.C. -/
theorem exists_reduced_representative_of_nsmul_eq_zero
    (theta : PhaseVector n) (hpres : C.Preserves theta)
    (U : C.ProjectiveDiagonalGroup)
    (hclass : C.projectiveClassMap ⟨theta, hpres⟩ = U)
    (hU : U ≠ 0) (d : ℕ) (hd : 0 < d) (hkill : d • theta = 0) :
    ∃ (R : ReducedDiagonalRepresentative n)
      (hRpres : C.Preserves R.phase),
      C.projectiveClassMap ⟨R.phase, hRpres⟩ = U ∧
      addOrderOf U ∣ R.q ∧
      R.q ∣ d ∧
      orderOf (diagonalGate R.phase) = R.q := by
  have htheta : theta ≠ 0 := by
    intro hzero
    have hrepzero :
        (⟨theta, hpres⟩ : C.preservingPhases) = 0 := by
      apply Subtype.ext
      exact hzero
    have : U = 0 := by
      rw [← hclass, hrepzero, map_zero]
    exact hU this
  have hfinite : IsOfFinAddOrder theta := by
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    exact ⟨d, hd, hkill⟩
  obtain ⟨R, hRphase⟩ :=
    exists_reducedDiagonalRepresentative theta hfinite htheta
  have hRpres : C.Preserves R.phase := by
    rw [hRphase]
    exact hpres
  have hRclass : C.projectiveClassMap ⟨R.phase, hRpres⟩ = U := by
    have hsubtype :
        (⟨R.phase, hRpres⟩ : C.preservingPhases) =
          ⟨theta, hpres⟩ := by
      apply Subtype.ext
      exact hRphase
    rw [hsubtype, hclass]
  have hqd : R.q ∣ d := by
    rw [← R.addOrderOf_phase, hRphase,
      addOrderOf_dvd_iff_nsmul_eq_zero]
    exact hkill
  have hmqd : addOrderOf U ∣ R.q :=
    C.projectiveOrder_dvd_of_mem_physicalRepresentativeOrders U
      (C.mem_physicalRepresentativeOrders U R hRpres hRclass)
  exact ⟨R, hRpres, hRclass, hmqd, hqd, R.orderOf_diagonalGate⟩

/-- Any positive annihilating denominator of a representative bounds the
minimal physical order of its nonzero projective class. -/
theorem minimalPhysicalOrder_le_of_nsmul_eq_zero
    (theta : PhaseVector n) (hpres : C.Preserves theta)
    (U : C.ProjectiveDiagonalGroup)
    (hclass : C.projectiveClassMap ⟨theta, hpres⟩ = U)
    (hU : U ≠ 0) (d : ℕ) (hd : 0 < d) (hkill : d • theta = 0) :
    C.minimalPhysicalOrder U ≤ d := by
  obtain ⟨R, hRpres, hRclass, _hmq, hqd, _hphysical⟩ :=
    C.exists_reduced_representative_of_nsmul_eq_zero
      theta hpres U hclass hU d hd hkill
  exact (C.minimalPhysicalOrder_le U R hRpres hRclass).trans
    (Nat.le_of_dvd hd hqd)

end CodeProjector

end

end QECC
