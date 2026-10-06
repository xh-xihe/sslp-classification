import MainTheory.D3AutomaticBoundedGenerator

/-!
# Outer-record entry from a bounded finite generator

The sharp sparse construction now produces a bounded primitive finite
generator.  This module isolates the remaining purely finite step: normalize
its angle by local `X` and a unit, prove that primitivity is preserved, sort
coordinates, and obtain a literal record in `primitiveRecords` while retaining
the exact modulus, logical order, and permutation witness.

No sparse pivot appears in this interface.  A pivot is one way to prove the
order bound; once `q <= 9` has already been proved for the freshly constructed
denominator, requiring another pivot would duplicate the mathematics and risk
relating the record to the wrong modulus.
-/

namespace MainTheory.D3BoundedOuterRecord

open MainTheory
open MainTheory.SixQubitSemanticEntrance

noncomputable section

/-- Multiplication of every coordinate by a unit preserves the exact gcd-style
primitivity predicate.  Divisibility is transported through the canonical
quotient `ZMod q -> ZMod d`; multiplying by the inverse unit recovers the
original residue. -/
theorem primitive_unit_mul {n q : ℕ} [NeZero q]
    (u : (ZMod q)ˣ) (a : Fin n → ZMod q)
    (hprimitive : Gate.Primitive q a) :
    Gate.Primitive q (fun j ↦ (u : ZMod q) * a j) := by
  intro d hdq hscaled
  apply hprimitive d hdq
  intro j
  let f : ZMod q →+* ZMod d := ZMod.castHom hdq (ZMod d)
  have hscaledZero : f ((u : ZMod q) * a j) = 0 := by
    change ZMod.castHom hdq (ZMod d) ((u : ZMod q) * a j) = 0
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_zero_iff _ _).2 (hscaled j)
  have hrecover :
      (↑(u⁻¹) : ZMod q) * ((u : ZMod q) * a j) = a j := by
    rw [← mul_assoc]
    simp
  have horiginalZero : f (a j) = 0 := by
    calc
      f (a j) =
          f ((↑(u⁻¹) : ZMod q) * ((u : ZMod q) * a j)) :=
        congrArg f hrecover.symm
      _ = f (↑(u⁻¹) : ZMod q) * f ((u : ZMod q) * a j) := by
        rw [map_mul]
      _ = 0 := by
        rw [hscaledZero, mul_zero]
  have hvalZero : ((a j).val : ZMod d) = 0 := by
    simpa only [f, ZMod.castHom_apply, ZMod.cast_eq_val] using
      horiginalZero
  exact (ZMod.natCast_eq_zero_iff _ _).1 hvalZero

/-- The normalized angle in every proved two-fibre certificate is primitive;
the unit rescaling cannot silently lower its physical order. -/
theorem normalizedFiniteAngle_primitive
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    Gate.Primitive q (normalizedFiniteAngle G T) := by
  simpa [normalizedFiniteAngle] using
    primitive_unit_mul T.unit (Normalize.flip G.angle T.x0)
      (Normalize.primitive_flip G.angle T.x0 G.primitive)

/-- Natural representatives of a normalized bounded generator angle. -/
def normalizedNatAngle
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    OuterEnumeration.Angle6 :=
  fun j ↦ (normalizedFiniteAngle G T j).val

theorem normalizedNatAngle_lt
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) (j : Fin 6) :
    normalizedNatAngle T j < q :=
  ZMod.val_lt _

/-- Sorting retains an explicit coordinate permutation and lands in the
executable primitive-angle list. -/
theorem exists_canonical_primitive_angle
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    {G : RankTwoGlobal.FiniteGeneratorResolution C q}
    (T : RankTwoGlobal.TwoFiberCertificate G) :
    ∃ (sigma : Equiv.Perm (Fin 6)) (a : OuterEnumeration.Angle6),
      a ∈ OuterEnumeration.primitiveAngles6 q ∧
      a = normalizedNatAngle T ∘ sigma ∧
      (fun j ↦ (a j : ZMod q)) =
        normalizedFiniteAngle G T ∘ sigma := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  obtain ⟨sigma, hweak⟩ :=
    OuterCompleteness.exists_permutation_mem_weakAngles6
      (normalizedNatAngle T) (normalizedNatAngle_lt T)
  let a : OuterEnumeration.Angle6 := normalizedNatAngle T ∘ sigma
  have hcast : (fun j ↦ (a j : ZMod q)) =
      normalizedFiniteAngle G T ∘ sigma := by
    funext j
    simp only [a, normalizedNatAngle, Function.comp_apply]
    simp [ZMod.natCast_val, ZMod.cast_id]
  have hprimitive : Gate.Primitive q
      (fun j ↦ (a j : ZMod q)) := by
    rw [hcast]
    exact primitive_comp_perm
      (normalizedFiniteAngle G T)
      (normalizedFiniteAngle_primitive T) sigma
  have hrange : ∀ j, a j < q := by
    intro j
    exact normalizedNatAngle_lt T (sigma j)
  have hbool : OuterEnumeration.IsPrimitive q a = true :=
    (OuterCompleteness.isPrimitive_iff_gatePrimitive hq a hrange).2
      hprimitive
  refine ⟨sigma, a, (mem_primitiveAngles6_iff).2 ⟨hweak, hbool⟩,
    rfl, hcast⟩

/-- Any already-bounded generator produces a literal finite outer record.
The matching fields in the conclusion prevent a vacuous unrelated-record
witness. -/
theorem exists_record_in_primitiveRecords
    {C : CodeSpec.ExactCode 6 2 3} {q : ℕ} [NeZero q]
    (G : RankTwoGlobal.FiniteGeneratorResolution C q)
    (T : RankTwoGlobal.TwoFiberCertificate G)
    (hq9 : q ≤ 9) :
    ∃ record : OuterEnumeration.RawRecord,
      record ∈ OuterEnumeration.primitiveRecords ∧
      record.q = q ∧
      record.m = T.logicalOrder ∧
      ∃ sigma : Equiv.Perm (Fin 6),
        record.a = normalizedNatAngle T ∘ sigma := by
  obtain ⟨sigma, a, ha, haeq, _⟩ :=
    exists_canonical_primitive_angle T
  have hqmem : q ∈ OuterEnumeration.sixQubitModuli :=
    mem_sixQubitModuli_of_bounds T.two_le_physicalOrder hq9
  have hm : T.logicalOrder ∈ OuterEnumeration.logicalOrders q :=
    mem_logicalOrders_of_order_data
      (Nat.pos_of_ne_zero (NeZero.ne q))
      T.two_le_logicalOrder T.logicalOrder_dvd_physical
  let record : OuterEnumeration.RawRecord :=
    { q := q, m := T.logicalOrder, a := a }
  have hrecord : record ∈ OuterEnumeration.primitiveRecords := by
    simp only [OuterEnumeration.primitiveRecords, List.mem_flatMap,
      List.mem_map]
    exact ⟨q, hqmem, T.logicalOrder, hm, a, ha, rfl⟩
  exact ⟨record, hrecord, rfl, rfl, sigma, haeq⟩

end

end MainTheory.D3BoundedOuterRecord
