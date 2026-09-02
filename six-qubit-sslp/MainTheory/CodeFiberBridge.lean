import MainTheory.D3BoundedNormalForm
import MainTheory.OuterCompleteness

/-!
# From a code to the enumerated fibre pair

`D3CertifiedSpectralOuterEntrance.code_with_nontrivial_diagonal_symmetry_enters_outer`
puts an exact `((6,2,3))` code into the outer enumeration, and its own docstring
says where it stops:

> The conclusion deliberately stops before final coordinate-permutation
> transport into generated orbit fibres.

What it delivers is `ExactOuterRecordStatement`, which is purely index-level:
there is a record with the right `(q, m)` whose angle is a permutation of the
code's.  Nothing said where the code's two *logical words* live.  That is the
one gap between the certified combinatorial chain
`13,877 -> ... -> 66` and a statement about codes: without it,
`thm:six-66-orbits` classifies a list, not a class of codes.

This file closes it, and the reason it is short is that
`SortedForm.SortedNormalForm` already did the work: its angle vector is
sorted and primitive -- the enumeration's own canonical form, so no further
permutation is needed -- and its two fibre clauses say exactly that the logical
words are supported in the residue fibres.  What remains is to read that off as
the generated pipeline's `FiberPair`.
-/

namespace MainTheory.CodeFiberBridge

open MainTheory
open MainTheory.OuterCompleteness
open MainTheory.SortedForm

noncomputable section

variable {C : CodeSpec.ExactCode 6 2 3}

/-- The outer-enumeration record read off a sorted normal form. -/
def recordOf (S : SortedNormalForm C) : OuterEnumeration.RawRecord :=
  ⟨S.q, S.m, fun j => (S.angle j).val⟩

@[simp] theorem recordOf_q (S : SortedNormalForm C) : (recordOf S).q = S.q := rfl
@[simp] theorem recordOf_m (S : SortedNormalForm C) : (recordOf S).m = S.m := rfl

/-- Casting the record's natural angle back into `ZMod q` returns the normal
form's angle: no information is lost in the passage to the enumeration. -/
theorem recordOf_cast (S : SortedNormalForm C) (j : Fin 6) :
    (((recordOf S).a j : ℕ) : ZMod (recordOf S).q) = S.angle j := by
  haveI := S.q_ne
  show (((S.angle j).val : ℕ) : ZMod S.q) = S.angle j
  simp [ZMod.natCast_val, ZMod.cast_id]

theorem recordOf_angleFun (S : SortedNormalForm C) :
    (fun j => (((recordOf S).a j : ℕ) : ZMod (recordOf S).q)) = S.angle := by
  funext j
  exact recordOf_cast S j

/-- **The record of a sorted normal form is one the enumeration lists.**

`q` is in range because the distance-three bound gives `q <= 9`; `m` is a
logical order because `2 <= m` and `m | q`; and the angle is one of the
enumerated primitive canonical vectors because it is sorted, in range and
primitive -- which is what the sorted normal form was built to supply. -/
theorem recordOf_mem (S : SortedNormalForm C) (hq9 : S.q ≤ 9) :
    recordOf S ∈ OuterEnumeration.primitiveRecords := by
  have hq2 : 2 ≤ S.q := S.two_le_q
  have hm2 : 2 ≤ S.m := S.two_le_m
  have hmq : S.m ∣ S.q := S.m_dvd_q
  have hqmem : S.q ∈ OuterEnumeration.sixQubitModuli :=
    SixQubitSemanticEntrance.mem_sixQubitModuli_of_bounds hq2 hq9
  have hmmem : S.m ∈ OuterEnumeration.logicalOrders S.q :=
    SixQubitSemanticEntrance.mem_logicalOrders_of_order_data
      (by omega : 0 < S.q) hm2 hmq
  have hrange : ∀ j, ((recordOf S).a j) < S.q := S.lt_q
  have hweak : (recordOf S).a ∈ OuterEnumeration.weakAngles6 S.q :=
    mem_weakAngles6_iff.2 ⟨hrange, S.sorted⟩
  have hprim : OuterEnumeration.IsPrimitive S.q ((recordOf S).a) = true := by
    refine (isPrimitive_iff_gatePrimitive (by omega : 0 < S.q) _ hrange).2 ?_
    have := S.primitive
    rwa [← recordOf_angleFun S] at this
  have hamem : (recordOf S).a ∈ OuterEnumeration.primitiveAngles6 S.q :=
    SixQubitSemanticEntrance.mem_primitiveAngles6_iff.2 ⟨hweak, hprim⟩
  simp only [OuterEnumeration.primitiveRecords, List.mem_flatMap, List.mem_map]
  exact ⟨S.q, hqmem, S.m, hmmem, (recordOf S).a, hamem, rfl⟩

/-- **The first logical word is supported in the zero-residue mask.** -/
theorem support_mask0 (S : SortedNormalForm C) (x : FinitePipeline.Word6)
    (hx : S.frame.vec 0 (wordBitString x) ≠ 0) :
    FinitePipeline.InMask (recordFiberPair (recordOf S)).mask0 x := by
  haveI := S.q_ne
  have hqpos : 0 < S.q := by have := S.two_le_q; omega
  have hw : SS.weight S.angle (wordBitString x) = 0 :=
    S.leftFiber (wordBitString x) hx
  rw [in_recordFiberPair_mask0_iff]
  have hmem : x ∈ gateResidueFiber (recordOf S) hqpos 0 := by
    rw [gateResidueFiber]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [recordOf_angleFun S, hw]
    simp
  exact (mem_gateResidueFiber_iff (recordOf S) hqpos 0 hqpos x).1 hmem

/-- **The second logical word is supported in the `q/m` residue mask.** -/
theorem support_mask1 (S : SortedNormalForm C) (x : FinitePipeline.Word6)
    (hx : S.frame.vec 1 (wordBitString x) ≠ 0) :
    FinitePipeline.InMask (recordFiberPair (recordOf S)).mask1 x := by
  haveI := S.q_ne
  have hqpos : 0 < S.q := by have := S.two_le_q; omega
  have hm1 : 1 < S.m := by have := S.two_le_m; omega
  have hlt : S.q / S.m < S.q := Nat.div_lt_self hqpos hm1
  have hw : SS.weight S.angle (wordBitString x) = ((S.q / S.m : ℕ) : ZMod S.q) :=
    S.rightFiber (wordBitString x) hx
  rw [in_recordFiberPair_mask1_iff]
  have hmem : x ∈ gateResidueFiber (recordOf S) hqpos (S.q / S.m) := by
    rw [gateResidueFiber]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [recordOf_angleFun S, hw]
  exact (mem_gateResidueFiber_iff (recordOf S) hqpos (S.q / S.m) hlt x).1 hmem

/-! ## Into the 12,768 nonempty-fibre records -/

set_option maxRecDepth 8000 in
/-- Every six-qubit Boolean string is the bit pattern of a pipeline word:
`wordBitString` is onto.  Both sides have sixty-four elements, so this is a
finite check. -/
theorem exists_word_bitString : ∀ s : SS.BitString 6,
    ∃ x : FinitePipeline.Word6, wordBitString x = s := by decide

/-- A unit vector is nonzero somewhere, and that somewhere is a pipeline
word. -/
theorem exists_support_word (S : SortedNormalForm C) :
    ∃ x : FinitePipeline.Word6, S.frame.vec 1 (wordBitString x) ≠ 0 := by
  by_contra h
  push_neg at h
  have hzero : S.frame.vec 1 = 0 := by
    funext s
    obtain ⟨x, hx⟩ := exists_word_bitString s
    rw [← hx]
    exact h x
  have hself := S.frame.orthonormal 1 1
  rw [hzero] at hself
  simp [SS.innerC] at hself

/-- **The record has a nonempty second fibre**, because the code's second
logical word lives there.  This is what carries the code from the 13,449
primitive records into the 12,768 that survive the fibre test. -/
theorem recordOf_hasSecondFiber (S : SortedNormalForm C) :
    OuterEnumeration.HasSecondFiber (recordOf S) = true := by
  rw [hasSecondFiber_iff_exists_word]
  obtain ⟨x, hx⟩ := exists_support_word S
  refine ⟨x, ?_⟩
  have := support_mask1 S x hx
  rwa [in_recordFiberPair_mask1_iff] at this

/-- **The record of a sorted normal form survives the fibre test.**

This is the membership the certified chain actually consumes: the 12,768-record
list `nonemptyFiberRecords` is the input to `PairProvenance`, and from there to
the 11,422 coarse pairs, the 508 cubes and the 66 orbit keys.  `recordOf_mem`
only reached the 13,449 primitive records. -/
theorem recordOf_mem_nonemptyFiber (S : SortedNormalForm C) (hq9 : S.q ≤ 9) :
    recordOf S ∈ OuterEnumeration.nonemptyFiberRecords := by
  have hq2 : 2 ≤ S.q := S.two_le_q
  have hqmem : S.q ∈ OuterEnumeration.sixQubitModuli :=
    SixQubitSemanticEntrance.mem_sixQubitModuli_of_bounds hq2 hq9
  have hmmem : S.m ∈ OuterEnumeration.logicalOrders S.q :=
    SixQubitSemanticEntrance.mem_logicalOrders_of_order_data
      (by omega : 0 < S.q) S.two_le_m S.m_dvd_q
  have hrange : ∀ j, ((recordOf S).a j) < S.q := S.lt_q
  have hweak : (recordOf S).a ∈ OuterEnumeration.weakAngles6 S.q :=
    mem_weakAngles6_iff.2 ⟨hrange, S.sorted⟩
  have hprim : OuterEnumeration.IsPrimitive S.q ((recordOf S).a) = true := by
    refine (isPrimitive_iff_gatePrimitive (by omega : 0 < S.q) _ hrange).2 ?_
    have := S.primitive
    rwa [← recordOf_angleFun S] at this
  rw [OuterEnumeration.weakAngles6] at hweak
  obtain ⟨a0, ha0, hchunk⟩ := List.mem_flatMap.1 hweak
  simp only [OuterEnumeration.nonemptyFiberRecords, List.mem_flatMap,
    List.mem_map]
  refine ⟨S.q, hqmem, S.m, hmmem, a0, ha0, (recordOf S).a, ?_, rfl⟩
  rw [OuterEnumeration.nonemptyAngleChunk]
  refine List.mem_filter.2 ⟨?_, ?_⟩
  · rw [OuterEnumeration.primitiveAngles6FromFirst]
    exact List.mem_filter.2 ⟨hchunk, hprim⟩
  · exact recordOf_hasSecondFiber S

/-- **The semantic bridge.**

Every exact `((6,2,3))` code carrying a projectively nontrivial diagonal
operation has, after a local `X` string and a permutation of the physical
qubits, its two logical words supported in the two residue fibres of a record
the outer enumeration actually lists -- with modulus at most nine.

This is what turns the certified chain `13,877 -> ... -> 66` from a statement
about a list into a statement about codes. -/
theorem code_supports_in_enumerated_fibres (C : CodeSpec.ExactCode 6 2 3)
    (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C,
      S.q ≤ 9 ∧
      recordOf S ∈ OuterEnumeration.primitiveRecords ∧
      (∀ x : FinitePipeline.Word6, S.frame.vec 0 (wordBitString x) ≠ 0 →
        FinitePipeline.InMask (recordFiberPair (recordOf S)).mask0 x) ∧
      (∀ x : FinitePipeline.Word6, S.frame.vec 1 (wordBitString x) ≠ 0 →
        FinitePipeline.InMask (recordFiberPair (recordOf S)).mask1 x) := by
  obtain ⟨S, hq9⟩ :=
    D3BoundedNormalForm.exists_sortedNormalForm_le_nine C theta hpres hnt
  exact ⟨S, hq9, recordOf_mem S hq9, support_mask0 S, support_mask1 S⟩

end

end MainTheory.CodeFiberBridge
