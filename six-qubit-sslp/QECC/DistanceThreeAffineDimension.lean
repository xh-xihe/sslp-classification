import QECC.DistanceThreePhaseSystem
import QECC.ActualSupportTransport

namespace QECC

noncomputable section

/-- The linear sign change underlying XOR on real zero-one coordinates. -/
def xorRealLinearEquiv {n : ℕ} (t : BitString n) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun v j := if t j then -v j else v j
  invFun v j := if t j then -v j else v j
  left_inv v := by
    funext j
    cases ht : t j <;> simp [ht]
  right_inv v := by
    funext j
    cases ht : t j <;> simp [ht]
  map_add' v w := by
    funext j
    cases ht : t j <;> simp [ht, add_comm]
  map_smul' c v := by
    funext j
    cases ht : t j <;> simp [ht]

/-- XOR on bit strings extends to an affine equivalence of the ambient real
coordinate spaces. -/
def xorRealAffineEquiv {n : ℕ} (t : BitString n) :
    (Fin n → ℝ) ≃ᵃ[ℝ] (Fin n → ℝ) where
  toFun v j := if t j then 1 - v j else v j
  invFun v j := if t j then 1 - v j else v j
  left_inv v := by
    funext j
    cases ht : t j <;> simp [ht]
  right_inv v := by
    funext j
    cases ht : t j <;> simp [ht]
  linear := xorRealLinearEquiv t
  map_vadd' p v := by
    funext j
    cases ht : t j
    · simp [xorRealLinearEquiv, ht]
    · simp [xorRealLinearEquiv, ht]
      abel

@[simp] theorem xorRealAffineEquiv_bitVector {n : ℕ}
    (t x : BitString n) :
    xorRealAffineEquiv t (bitVector x) = bitVector (xorEquiv t x) := by
  funext j
  cases ht : t j <;> cases hx : x j <;>
    simp [xorRealAffineEquiv, bitVector, bitReal, xorEquiv, ht, hx]

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- Real affine dimension of an actual active-sector support. -/
def actualSectorAffineDimension (a : Fin n → ZMod q)
    (b : C.ActiveResidue a) : ℕ :=
  Module.finrank ℝ (C.actualSectorAffineSpan a b).direction

/-- If the zero bit string lies in an actual support, its affine direction is
the real row span of the binary support matrix. -/
theorem direction_actualSectorAffineSpan_eq_rowSpan
    (a : Fin n → ZMod q) (b : C.ActiveResidue a)
    (hzero : (0 : BitString n) ∈ C.actualSectorSupport a b) :
    (C.actualSectorAffineSpan a b).direction =
      Submodule.span ℝ (Set.range
        ((C.anchorActualSupportMatrix a b).map
          (Int.castRingHom ℝ)).row) := by
  exact C.direction_actualSectorAffineSpan_eq_anchorRowSpan a b hzero

/-- The rank `r` in the normalized distance-three certificate is exactly the
real affine dimension of its anchor actual support. -/
theorem NormalizedDistanceThreePhaseSystem.r_eq_actualSectorAffineDimension
    [NeZero q] {hq : 0 < q} {a : Fin n → ZMod q}
    {b0 b1 : C.ActiveResidue a}
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    D.r = C.actualSectorAffineDimension a b0 := by
  exact D.r_eq_realAffineDimension

/-- The same `r` is also the real affine dimension of the second actual
support. -/
theorem NormalizedDistanceThreePhaseSystem.r_eq_secondActualSectorAffineDimension
    [NeZero q] {hq : 0 < q} {a : Fin n → ZMod q}
    {b0 b1 : C.ActiveResidue a}
    (D : C.NormalizedDistanceThreePhaseSystem hq a b0 b1) :
    D.r = C.actualSectorAffineDimension a b1 := by
  exact D.r_eq_secondRealAffineDimension

/-- XOR maps the embedded positive support of an active sector exactly by
the ambient real affine equivalence. -/
theorem image_positiveSupport_xor
    (a : Fin n → ZMod q) (t : BitString n)
    (b : C.ActiveResidue a) :
    xorRealAffineEquiv t ''
        (bitVector '' C.actualSectorSupport a b) =
      bitVector ''
        (C.reindex (xorEquiv t)).actualSectorSupport (xorCoefficient t a)
          (C.xorActiveResidueEquiv a t b) := by
  ext v
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨xorEquiv t x, ?_, by simp⟩
    exact (C.mem_actualSectorSupport_xor_iff a t b x).2 hx
  · rintro ⟨y, hy, rfl⟩
    let x := xorEquiv t y
    have hinv : xorEquiv t x = y := by
      dsimp [x]
      funext j
      simp
    have hx : x ∈ C.actualSectorSupport a b := by
      apply (C.mem_actualSectorSupport_xor_iff a t b x).1
      simpa [hinv] using hy
    refine ⟨bitVector x, ⟨x, hx, rfl⟩, ?_⟩
    rw [xorRealAffineEquiv_bitVector, hinv]

/-- The actual-sector affine span itself is transported by the ambient XOR
affine equivalence. -/
theorem actualSectorAffineSpan_xor
    (a : Fin n → ZMod q) (t : BitString n)
    (b : C.ActiveResidue a) :
    (C.actualSectorAffineSpan a b).map (xorRealAffineEquiv t).toAffineMap =
      (C.reindex (xorEquiv t)).actualSectorAffineSpan (xorCoefficient t a)
        (C.xorActiveResidueEquiv a t b) := by
  unfold actualSectorAffineSpan
  rw [AffineSubspace.map_span]
  simpa only using congrArg (affineSpan ℝ)
    (C.image_positiveSupport_xor a t b)

/-- Local-X normalization preserves the real affine dimension of every
actual sector support. -/
theorem actualSectorAffineDimension_xor
    (a : Fin n → ZMod q) (t : BitString n)
    (b : C.ActiveResidue a) :
    (C.reindex (xorEquiv t)).actualSectorAffineDimension (xorCoefficient t a)
        (C.xorActiveResidueEquiv a t b) =
      C.actualSectorAffineDimension a b := by
  unfold actualSectorAffineDimension
  rw [← C.actualSectorAffineSpan_xor a t b,
    AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq (xorRealAffineEquiv t).linear _

end CodeProjector

end

end QECC
