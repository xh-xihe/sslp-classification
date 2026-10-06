import QECC.PauliTransport
import QECC.SectorProbabilities

namespace QECC

noncomputable section

/-- Under local-X basis relabelling, a number operator is either unchanged
or replaced by its complement. -/
theorem reindexOperator_xor_numberOp {n : ℕ}
    (t : BitString n) (j : Fin n) :
    reindexOperator (xorEquiv t) (numberOp j) =
      if t j then 1 - numberOp j else numberOp j := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    cases ht : t j <;> cases hx : x j <;>
      simp [reindexOperator, Matrix.reindex_apply, numberOp, xorEquiv, ht, hx]
  · have he : xorEquiv t x ≠ xorEquiv t y :=
      (xorEquiv t).injective.ne hxy
    cases ht : t j <;>
      simp [reindexOperator, Matrix.reindex_apply, numberOp, hxy, he]

namespace CodeProjector

variable {n K : ℕ}

/-- Detection of all single-coordinate number operators is invariant under
local-X relabelling.  A flipped coordinate changes its detected mean from
`mu` to `1 - mu`. -/
theorem detectsNumberOps_reindex_xor (C : CodeProjector n K)
    (t : BitString n) (hdetect : C.DetectsNumberOps) :
    (C.reindex (xorEquiv t)).DetectsNumberOps := by
  rcases hdetect with ⟨mu, hmu⟩
  let C' := C.reindex (xorEquiv t)
  refine ⟨fun j => if t j then 1 - mu j else mu j, fun j => ?_⟩
  let R := Matrix.reindexAlgEquiv ℂ ℂ (xorEquiv t)
  have htransport :
      C'.proj * reindexOperator (xorEquiv t) (numberOp j) * C'.proj =
        (mu j : ℂ) • C'.proj := by
    change R C.proj * R (numberOp j) * R C.proj =
      (mu j : ℂ) • R C.proj
    rw [← map_mul, ← map_mul, hmu]
    exact map_smul R (mu j : ℂ) C.proj
  cases ht : t j
  · simpa [ht, reindexOperator_xor_numberOp, C'] using htransport
  · rw [reindexOperator_xor_numberOp, if_pos ht] at htransport
    have hsub :
        C'.proj - C'.proj * numberOp j * C'.proj =
          (mu j : ℂ) • C'.proj := by
      simpa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, C'.idempotent]
        using htransport
    have htargetComplex :
        C'.proj * numberOp j * C'.proj =
          ((1 : ℂ) - (mu j : ℂ)) • C'.proj := by
      rw [sub_smul, one_smul]
      apply (eq_sub_iff_add_eq).2
      simpa [add_comm] using ((sub_eq_iff_eq_add).mp hsub).symm
    have hcast : ((1 : ℂ) - (mu j : ℂ)) =
        (((1 - mu j : ℝ) : ℂ)) := by
      push_cast
      rfl
    rw [hcast] at htargetComplex
    simpa [ht] using htargetComplex

end CodeProjector

end

end QECC
