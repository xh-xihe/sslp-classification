import QECC.ProjectorSupport
import QECC.SectorTransport

namespace QECC

noncomputable section

namespace CodeProjector

variable {n K q : ℕ} (C : CodeProjector n K)

/-- Local-X transport carries the normalized diagonal distribution of an
active sector to the translated active sector. -/
theorem sectorDistribution_xor (a : Fin n → ZMod q) (t : BitString n)
    (b : C.ActiveResidue a) (x : BitString n) :
    (C.reindex (xorEquiv t)).sectorDistribution (xorCoefficient t a)
      (C.xorActiveResidueEquiv a t b) (xorEquiv t x) =
      C.sectorDistribution a b x := by
  unfold sectorDistribution sectorDimension
  simp only [xorActiveResidueEquiv_apply_val]
  rw [← C.finrank_xorPhaseSector a t b.1]
  congr 1
  simp only [sectorProjector_apply, reindex_proj_apply, xorEquiv_symm]
  have hiff : subsetSum (xorCoefficient t a) (xorEquiv t x) =
      b.1 - subsetSum a t ↔ subsetSum a x = b.1 := by
    change xorEquiv t x ∈ subsetSumFiber (xorCoefficient t a)
      (b.1 - subsetSum a t) ↔ x ∈ subsetSumFiber a b.1
    rw [← image_subsetSumFiber_xorEquiv a t b.1,
      Set.mem_image_equiv, xorEquiv_symm]
    have hinv : xorEquiv t (xorEquiv t x) = x := by
      funext j
      simp
    rw [hinv]
  by_cases hx : subsetSum a x = b.1
  · rw [if_pos hx, if_pos (hiff.2 hx)]
    simp [xorEquiv]
  · rw [if_neg hx, if_neg (not_congr hiff |>.2 hx)]

/-- Membership in the positive actual support is preserved and reflected by
local-X transport. -/
theorem mem_actualSectorSupport_xor_iff
    (a : Fin n → ZMod q) (t : BitString n)
    (b : C.ActiveResidue a) (x : BitString n) :
    xorEquiv t x ∈
        (C.reindex (xorEquiv t)).actualSectorSupport (xorCoefficient t a)
          (C.xorActiveResidueEquiv a t b) ↔
      x ∈ C.actualSectorSupport a b := by
  change 0 <
      (C.reindex (xorEquiv t)).sectorDistribution (xorCoefficient t a)
        (C.xorActiveResidueEquiv a t b) (xorEquiv t x) ↔
    0 < C.sectorDistribution a b x
  rw [C.sectorDistribution_xor]

/-- Local-X transport sends an actual sector support exactly onto the
corresponding translated actual support. -/
theorem image_actualSectorSupport_xor
    (a : Fin n → ZMod q) (t : BitString n)
    (b : C.ActiveResidue a) :
    xorEquiv t '' C.actualSectorSupport a b =
      (C.reindex (xorEquiv t)).actualSectorSupport (xorCoefficient t a)
        (C.xorActiveResidueEquiv a t b) := by
  ext y
  rw [Set.mem_image_equiv, xorEquiv_symm]
  have h := C.mem_actualSectorSupport_xor_iff a t b (xorEquiv t y)
  have hinv : xorEquiv t (xorEquiv t y) = y := by
    funext j
    simp
  rw [hinv] at h
  exact h.symm

/-- Choosing an actual support point as the XOR origin sends it to the zero
bit string in the translated actual support. -/
theorem zero_mem_transported_actualSectorSupport
    (a : Fin n → ZMod q) (t : BitString n)
    (b : C.ActiveResidue a) (ht : t ∈ C.actualSectorSupport a b) :
    (0 : BitString n) ∈
      (C.reindex (xorEquiv t)).actualSectorSupport (xorCoefficient t a)
        (C.xorActiveResidueEquiv a t b) := by
  have hmem := (C.mem_actualSectorSupport_xor_iff a t b t).2 ht
  simpa using hmem

/-- The transported label of a sector whose chosen support point is the XOR
origin is zero. -/
theorem transported_anchor_val_eq_zero
    (a : Fin n → ZMod q) (t : BitString n)
    (b : C.ActiveResidue a) (ht : t ∈ C.actualSectorSupport a b) :
    (C.xorActiveResidueEquiv a t b).1 = 0 := by
  rw [xorActiveResidueEquiv_apply_val]
  have htFiber := C.actualSectorSupport_subset_fiber a b ht
  rw [htFiber, sub_self]

end CodeProjector

end

end QECC
