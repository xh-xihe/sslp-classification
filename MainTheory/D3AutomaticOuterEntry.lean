import MainTheory.D3BoundedOuterRecord

/-!
# Automatic outer entry for a supplied finite generator

This is the composition of the fully proved distance-three chain:

* normalize a genuine primitive finite generator;
* construct the fresh sparse rational phase;
* package it at its own least denominator;
* prove that denominator is at most nine;
* normalize the fresh generator and place its angle in the executable outer
  record list.

The resulting record retains the exact fresh modulus, logical order, and
coordinate-permutation witness.  It still does not transport the normalized
logical states through that final coordinate permutation; that separate
state/fibre transport remains visible in the theorem's scope.
-/

namespace MainTheory.D3AutomaticOuterEntry

open MainTheory
open MainTheory.D3FreshSparseAssembly
open MainTheory.D3NormalizedFreshPhase
open MainTheory.D3AutomaticBoundedGenerator
open MainTheory.D3BoundedOuterRecord

noncomputable section

/-- The proved two-fibre normalization of the freshly constructed bounded
generator.  Its dependent fresh-order instance is explicit in the result
type and is derived from denominator positivity. -/
def automaticFreshTwoFiber
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    @RankTwoGlobal.TwoFiberCertificate 6 3
      (frameFreshSparsePhase T).data.order
      (frameFreshOrderNeZero T)
      (normalizedCode T)
      (automaticFreshGenerator T) := by
  letI : NeZero (frameFreshSparsePhase T).data.order :=
    frameFreshOrderNeZero T
  exact canonicalTwoFiber (automaticFreshGenerator T)

/-- Fresh logical order, exposed without making callers reconstruct the
dependent `NeZero` instance. -/
def automaticFreshLogicalOrder
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) : ℕ := by
  letI : NeZero (frameFreshSparsePhase T).data.order :=
    frameFreshOrderNeZero T
  exact (automaticFreshTwoFiber T).logicalOrder

/-- Natural representatives of the twice-normalized fresh angle, with the
same instance-free interface. -/
def automaticFreshNatAngle
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    OuterEnumeration.Angle6 := by
  letI : NeZero (frameFreshSparsePhase T).data.order :=
    frameFreshOrderNeZero T
  exact normalizedNatAngle (automaticFreshTwoFiber T)

/-- End-to-end finite-generator-to-outer-index theorem at distance three.
The record is tied to the fresh least denominator and returned normal form;
it cannot be witnessed by an unrelated element of `primitiveRecords`. -/
theorem twoFiber_enters_primitive_outer_index
    (betaSix : BinaryBeta.BetaBound 6 9)
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    2 ≤ (frameFreshSparsePhase T).data.order ∧
    (frameFreshSparsePhase T).data.order ≤ 9 ∧
    ∃ record : OuterEnumeration.RawRecord,
      record ∈ OuterEnumeration.primitiveRecords ∧
      record.q = (frameFreshSparsePhase T).data.order ∧
      record.m = automaticFreshLogicalOrder T ∧
      ∃ sigma : Equiv.Perm (Fin 6),
        record.a = automaticFreshNatAngle T ∘ sigma := by
  letI : NeZero (frameFreshSparsePhase T).data.order :=
    frameFreshOrderNeZero T
  let Tfresh := automaticFreshTwoFiber T
  have hq2 : 2 ≤ (frameFreshSparsePhase T).data.order :=
    Tfresh.two_le_physicalOrder
  have hq9 : (frameFreshSparsePhase T).data.order ≤ 9 :=
    automaticFreshGenerator_order_le_nine betaSix T
  obtain ⟨record, hrecord, hq, hm, sigma, ha⟩ :=
    exists_record_in_primitiveRecords
      (automaticFreshGenerator T) Tfresh hq9
  have hm' : record.m = automaticFreshLogicalOrder T := by
    simpa [automaticFreshLogicalOrder, Tfresh] using hm
  have ha' : record.a = automaticFreshNatAngle T ∘ sigma := by
    simpa [automaticFreshNatAngle, Tfresh] using ha
  exact ⟨hq2, hq9, record, hrecord, hq, hm', sigma, ha'⟩

/-- Generator-only form: even the first two-fibre certificate is chosen from
the kernel-proved existence theorem. -/
theorem finiteGenerator_enters_primitive_outer_index
    (betaSix : BinaryBeta.BetaBound 6 9)
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    (G : RankTwoGlobal.FiniteGeneratorResolution C q) :
    2 ≤ (frameFreshSparsePhase (canonicalTwoFiber G)).data.order ∧
    (frameFreshSparsePhase (canonicalTwoFiber G)).data.order ≤ 9 ∧
    ∃ record : OuterEnumeration.RawRecord,
      record ∈ OuterEnumeration.primitiveRecords ∧
      record.q =
        (frameFreshSparsePhase (canonicalTwoFiber G)).data.order ∧
      record.m = automaticFreshLogicalOrder (canonicalTwoFiber G) ∧
      ∃ sigma : Equiv.Perm (Fin 6),
        record.a =
          automaticFreshNatAngle (canonicalTwoFiber G) ∘ sigma :=
  twoFiber_enters_primitive_outer_index betaSix (canonicalTwoFiber G)

end

end MainTheory.D3AutomaticOuterEntry
