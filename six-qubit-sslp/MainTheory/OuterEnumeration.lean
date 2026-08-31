import Mathlib

/-!
# Kernel-checked six-qubit outer enumeration

This file implements the finite outer loop in Section 6 of `main.tex` without
enumerating the ambient type `Fin 6 → Fin q`.  The latter contains `q^6`
functions and made the larger `q` computations in `OuterIndex.lean` exhaust the
elaborator stack.  Here the generator constructs only weakly increasing
six-tuples, of which there are `Nat.choose (q + 5) 6`.

Every count theorem below is proved by ordinary kernel reduction (`decide`),
never by `native_decide` or an external evaluator.  The `12,768` second-fiber
count is split into bounded first-coordinate chunks so that no single proof
term contains the whole enumeration.
-/

namespace MainTheory.OuterEnumeration

/-! ## Weakly increasing angle vectors -/

/-- A six-qubit angle vector.  Values are kept as natural numbers; the
generator below enforces that every entry is strictly below its modulus. -/
abbrev Angle6 := Fin 6 → ℕ

/-- The explicit six-entry constructor used by the small enumerator. -/
def angle6 (a₀ a₁ a₂ a₃ a₄ a₅ : ℕ) : Angle6 :=
  ![a₀, a₁, a₂, a₃, a₄, a₅]

/-- The chunk whose first angle is the specified value `a₀`. -/
def weakAngles6FromFirst (q a₀ : ℕ) : List Angle6 :=
  (List.range' a₀ (q - a₀)).flatMap fun a₁ =>
    (List.range' a₁ (q - a₁)).flatMap fun a₂ =>
      (List.range' a₂ (q - a₂)).flatMap fun a₃ =>
        (List.range' a₃ (q - a₃)).flatMap fun a₄ =>
          (List.range' a₄ (q - a₄)).map fun a₅ =>
            angle6 a₀ a₁ a₂ a₃ a₄ a₅

/-- All weakly increasing length-six vectors with entries in `{0, ..., q-1}`.

The nested ranges visit only valid sorted vectors.  In particular, for `q = 9`
this constructs `3003` vectors instead of filtering all `9^6 = 531441`
functions. -/
def weakAngles6 (q : ℕ) : List Angle6 :=
  (List.range q).flatMap (weakAngles6FromFirst q)

/-- The common gcd of the modulus and all six entries. -/
def angleGCD (q : ℕ) (a : Angle6) : ℕ :=
  Nat.gcd q (Nat.gcd (a 0) (Nat.gcd (a 1) (Nat.gcd (a 2)
    (Nat.gcd (a 3) (Nat.gcd (a 4) (a 5))))))

/-- Primitivity of an angle representative. -/
def IsPrimitive (q : ℕ) (a : Angle6) : Bool := angleGCD q a == 1

/-- One primitive first-coordinate chunk. -/
def primitiveAngles6FromFirst (q a₀ : ℕ) : List Angle6 :=
  (weakAngles6FromFirst q a₀).filter (IsPrimitive q)

/-- The primitive sorted angle vectors for a fixed modulus.  Keeping the
first-coordinate chunks explicit is what lets the kernel check the largest
case without ever comparing one enormous elaborated expression. -/
def primitiveAngles6 (q : ℕ) : List Angle6 :=
  (List.range q).flatMap (primitiveAngles6FromFirst q)

/-! The following streaming counters mirror the generator but never construct
the six-tuples.  Their recursion depth is bounded by six plus the length of one
short range, so kernel evaluation stays stack-safe for all moduli used here. -/

/-- Count weakly increasing continuations of length `slots`, whose next entry
is at least `lo` and strictly below `q`. -/
def sortedCountFrom (q : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | slots + 1, lo =>
      (List.range' lo (q - lo)).foldl
        (fun total value => total + sortedCountFrom q slots value) 0

/-- Stack-safe count of weakly increasing six-angle vectors. -/
def sortedCount6 (q : ℕ) : ℕ := sortedCountFrom q 6 0

/-- Count primitive continuations while carrying the gcd accumulated so far. -/
def primitiveCountFrom (q : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, g => if g = 1 then 1 else 0
  | slots + 1, lo, g =>
      (List.range' lo (q - lo)).foldl
        (fun total value => total + primitiveCountFrom q slots value (Nat.gcd g value)) 0

/-- Stack-safe count of primitive weakly increasing six-angle vectors. -/
def primitiveCount6 (q : ℕ) : ℕ := primitiveCountFrom q 6 0 q

/-! ## The finite outer records -/

/-- One record in the outer loop: lift order `q`, nontrivial logical order
`m ∣ q`, and a sorted angle vector. -/
structure RawRecord where
  q : ℕ
  m : ℕ
  a : Angle6
  deriving DecidableEq

/-- The moduli used in the six-qubit classification: `2, ..., 9`. -/
def sixQubitModuli : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9]

/-- All nontrivial divisors `m > 1` of `q`, including `q` itself. -/
def logicalOrders (q : ℕ) : List ℕ :=
  (List.range' 2 (q - 1)).filter fun m => q % m == 0

/-- The complete raw outer index used in `main.tex`: `2 ≤ q ≤ 9`,
`1 < m ∣ q`, and a weakly increasing six-angle vector modulo `q`. -/
def rawRecords : List RawRecord :=
  sixQubitModuli.flatMap fun q =>
    (logicalOrders q).flatMap fun m =>
      (weakAngles6 q).map fun a => ⟨q, m, a⟩

/-- The sub-index in which the displayed lift is already faithful (`q = m`). -/
def faithfulRawRecords : List RawRecord :=
  sixQubitModuli.flatMap fun q =>
    (weakAngles6 q).map fun a => ⟨q, q, a⟩

/-- The primitive outer index, after removing common rescalings of `(q,a)`. -/
def primitiveRecords : List RawRecord :=
  sixQubitModuli.flatMap fun q =>
    (logicalOrders q).flatMap fun m =>
      (primitiveAngles6 q).map fun a => ⟨q, m, a⟩

/-! ## Kernel-checked counts -/

theorem sorted_two_list_agrees : (weakAngles6 2).length = sortedCount6 2 := by decide

theorem sorted_three_list_agrees : (weakAngles6 3).length = sortedCount6 3 := by decide

theorem sorted_four_list_agrees : (weakAngles6 4).length = sortedCount6 4 := by decide

set_option maxRecDepth 1000000 in
theorem sorted_five_list_agrees : (weakAngles6 5).length = sortedCount6 5 := by decide

set_option maxRecDepth 1000000 in
theorem sorted_six_list_agrees : (weakAngles6 6).length = sortedCount6 6 := by decide

set_option maxRecDepth 1000000 in
theorem sorted_seven_list_agrees : (weakAngles6 7).length = sortedCount6 7 := by decide

set_option maxRecDepth 1000000 in
theorem sorted_eight_list_agrees : (weakAngles6 8).length = sortedCount6 8 := by decide

set_option maxRecDepth 1000000 in
theorem sorted_nine_chunk_counts :
    (List.range 9).map (fun a₀ => (weakAngles6FromFirst 9 a₀).length) =
      [1287, 792, 462, 252, 126, 56, 21, 6, 1] := by decide

theorem sorted_nine_list_agrees : (weakAngles6 9).length = sortedCount6 9 := by
  simp only [weakAngles6, List.length_flatMap]
  rw [sorted_nine_chunk_counts]
  decide

set_option maxRecDepth 1000000 in
theorem primitive_two : (primitiveAngles6 2).length = 6 := by decide

theorem primitive_two_list_agrees : (primitiveAngles6 2).length = primitiveCount6 2 := by decide

set_option maxRecDepth 1000000 in
theorem primitive_three : (primitiveAngles6 3).length = 27 := by decide

theorem primitive_three_list_agrees :
    (primitiveAngles6 3).length = primitiveCount6 3 := by decide

set_option maxRecDepth 1000000 in
theorem primitive_four : (primitiveAngles6 4).length = 77 := by decide

theorem primitive_four_list_agrees :
    (primitiveAngles6 4).length = primitiveCount6 4 := by decide

set_option maxRecDepth 1000000 in
theorem primitive_five : (primitiveAngles6 5).length = 209 := by decide

set_option maxRecDepth 1000000 in
theorem primitive_five_list_agrees :
    (primitiveAngles6 5).length = primitiveCount6 5 := by decide

-- The larger four counts are checked below by a stack-safe streaming counter.

theorem primitive_six : primitiveCount6 6 = 428 := by decide

set_option maxRecDepth 1000000 in
theorem primitive_six_list_agrees : (primitiveAngles6 6).length = primitiveCount6 6 := by decide

theorem primitive_six_exact : (primitiveAngles6 6).length = 428 :=
  primitive_six_list_agrees.trans primitive_six

theorem primitive_seven : primitiveCount6 7 = 923 := by decide

set_option maxRecDepth 1000000 in
theorem primitive_seven_list_agrees : (primitiveAngles6 7).length = primitiveCount6 7 := by decide

theorem primitive_seven_exact : (primitiveAngles6 7).length = 923 :=
  primitive_seven_list_agrees.trans primitive_seven

theorem primitive_eight : primitiveCount6 8 = 1632 := by decide

set_option maxRecDepth 1000000 in
theorem primitive_eight_list_agrees : (primitiveAngles6 8).length = primitiveCount6 8 := by decide

theorem primitive_eight_exact : (primitiveAngles6 8).length = 1632 :=
  primitive_eight_list_agrees.trans primitive_eight

theorem primitive_nine : primitiveCount6 9 = 2975 := by decide

set_option maxRecDepth 1000000 in
theorem primitive_nine_chunk_counts :
    (List.range 9).map (fun a₀ => (primitiveAngles6FromFirst 9 a₀).length) =
      [1266, 792, 462, 246, 126, 56, 20, 6, 1] := by decide

theorem primitive_nine_list_agrees :
    (primitiveAngles6 9).length = primitiveCount6 9 := by
  simp only [primitiveAngles6, List.length_flatMap]
  rw [primitive_nine_chunk_counts]
  decide

theorem primitive_nine_exact : (primitiveAngles6 9).length = 2975 :=
  primitive_nine_list_agrees.trans primitive_nine

/- Equation `six:eq:outercount`: the raw sorted outer loop has `13,877`
records when the admissible logical orders are included. -/
/-- The number of raw records, evaluated without materializing record payloads. -/
def rawRecordCount : ℕ :=
  sixQubitModuli.foldl
    (fun total q => total + (logicalOrders q).length * sortedCount6 q) 0

/-- The streaming count is exactly the length of the explicit enumeration. -/
theorem rawRecords_length_eq_count : rawRecords.length = rawRecordCount := by
  simp only [rawRecords, List.length_flatMap, List.length_map]
  simp [sixQubitModuli, logicalOrders, rawRecordCount,
    sorted_two_list_agrees, sorted_three_list_agrees, sorted_four_list_agrees,
    sorted_five_list_agrees, sorted_six_list_agrees, sorted_seven_list_agrees,
    sorted_eight_list_agrees, sorted_nine_list_agrees, Nat.add_assoc]

/-- Equation `six:eq:outercount`, checked by kernel reduction. -/
theorem raw_record_count : rawRecordCount = 13877 := by decide

theorem raw_records_exact : rawRecords.length = 13877 :=
  rawRecords_length_eq_count.trans raw_record_count

/- The `q = m` part of the raw outer loop has `6,434` records. -/
/-- There is one faithful choice `m=q` per modulus. -/
def faithfulRawRecordCount : ℕ :=
  sixQubitModuli.foldl (fun total q => total + sortedCount6 q) 0

theorem faithfulRawRecords_length_eq_count :
    faithfulRawRecords.length = faithfulRawRecordCount := by
  simp only [faithfulRawRecords, List.length_flatMap, List.length_map]
  simp [sixQubitModuli, faithfulRawRecordCount,
    sorted_two_list_agrees, sorted_three_list_agrees, sorted_four_list_agrees,
    sorted_five_list_agrees, sorted_six_list_agrees, sorted_seven_list_agrees,
    sorted_eight_list_agrees, sorted_nine_list_agrees, Nat.add_assoc]

theorem faithful_raw_record_count : faithfulRawRecordCount = 6434 := by decide

theorem faithful_raw_records_exact : faithfulRawRecords.length = 6434 :=
  faithfulRawRecords_length_eq_count.trans faithful_raw_record_count

/- Equation `six:eq:primitiveTotal`: primitive reduction leaves `13,449`
records. -/
/-- The number of primitive records, with the same logical-order weights. -/
def primitiveRecordCount : ℕ :=
  sixQubitModuli.foldl
    (fun total q => total + (logicalOrders q).length * primitiveCount6 q) 0

theorem primitiveRecords_length_eq_count :
    primitiveRecords.length = primitiveRecordCount := by
  simp only [primitiveRecords, List.length_flatMap, List.length_map]
  simp [sixQubitModuli, logicalOrders, primitiveRecordCount,
    primitive_two_list_agrees, primitive_three_list_agrees,
    primitive_four_list_agrees, primitive_five_list_agrees,
    primitive_six_list_agrees, primitive_seven_list_agrees,
    primitive_eight_list_agrees, primitive_nine_list_agrees, Nat.add_assoc]

/-- Equation `six:eq:primitiveTotal`, checked by kernel reduction. -/
theorem primitive_record_count : primitiveRecordCount = 13449 := by decide

theorem primitive_records_exact : primitiveRecords.length = 13449 :=
  primitiveRecords_length_eq_count.trans primitive_record_count

/-! ## Nonempty second fibers -/

/-- The modular subset sum of `a` selected by the low six bits of `mask`. -/
def subsetSum (a : Angle6) (mask : ℕ) : ℕ :=
  (if mask.testBit 0 then a 0 else 0) +
  (if mask.testBit 1 then a 1 else 0) +
  (if mask.testBit 2 then a 2 else 0) +
  (if mask.testBit 3 then a 3 else 0) +
  (if mask.testBit 4 then a 4 else 0) +
  (if mask.testBit 5 then a 5 else 0)

/-- Direct 64-mask specification of second-fiber nonemptiness.  This remains a
small executable reference implementation. -/
def HasSecondFiberByMasks (r : RawRecord) : Bool :=
  (List.range 64).any fun mask => subsetSum r.a mask % r.q == r.q / r.m

/-- Residues reachable by choosing or omitting every entry in a list. -/
def reachableResidues (q : ℕ) : List ℕ → List ℕ
  | [] => [0]
  | value :: rest =>
      let old := reachableResidues q rest
      old ++ old.map (fun residue => (value + residue) % q)

/-- The exact inductive subset-sum semantics mirrored by `reachableResidues`. -/
def IsSubsetResidue (q : ℕ) : List ℕ → ℕ → Prop
  | [], target => target = 0
  | value :: rest, target =>
      IsSubsetResidue q rest target ∨
        ∃ residue, IsSubsetResidue q rest residue ∧ target = (value + residue) % q

/-- The evaluator has exactly the inductive subset-sum meaning. -/
theorem mem_reachableResidues_iff (q target : ℕ) (values : List ℕ) :
    target ∈ reachableResidues q values ↔ IsSubsetResidue q values target := by
  induction values generalizing target with
  | nil => simp [reachableResidues, IsSubsetResidue]
  | cons value rest ih =>
      simp only [reachableResidues, List.mem_append, List.mem_map, IsSubsetResidue]
      constructor
      · rintro (hold | ⟨residue, hresidue, heq⟩)
        · exact Or.inl ((ih target).mp hold)
        · exact Or.inr ⟨residue, (ih residue).mp hresidue, heq.symm⟩
      · rintro (hold | ⟨residue, hresidue, heq⟩)
        · exact Or.inl ((ih target).mpr hold)
        · exact Or.inr ⟨residue, (ih residue).mpr hresidue, heq.symm⟩

/-- Whether the second logical residue fiber `S_{q/m}` is nonempty. -/
def HasSecondFiber (r : RawRecord) : Bool :=
  (reachableResidues r.q [r.a 0, r.a 1, r.a 2, r.a 3, r.a 4, r.a 5]).contains
    (r.q / r.m)

/-- Primitive outer records for which both logical fibers can be populated.
The first fiber is automatic because the zero bit string has subset sum zero. -/
def nonemptyAngleChunk (q m a₀ : ℕ) : List Angle6 :=
  (primitiveAngles6FromFirst q a₀).filter fun a =>
    HasSecondFiber ⟨q, m, a⟩

/-- The surviving enumeration, kept in first-coordinate chunks for bounded
kernel reduction depth. -/
def nonemptyFiberRecords : List RawRecord :=
  sixQubitModuli.flatMap fun q =>
    (logicalOrders q).flatMap fun m =>
      (List.range q).flatMap fun a₀ =>
        (nonemptyAngleChunk q m a₀).map fun a => ⟨q, m, a⟩

/- Equation `six:eq:nonemptyrecords`: exactly `12,768` primitive records have
a nonempty second fiber. -/
/-- The count of one fixed `(q,m)` pair.  It is deliberately expressed as the
sum of the same first-coordinate chunks used by `nonemptyFiberRecords`. -/
def nonemptyFiberPairCount (q m : ℕ) : ℕ :=
  ((List.range q).map fun a₀ => (nonemptyAngleChunk q m a₀).length).sum

/-- A streaming count of the surviving first-coordinate chunks. -/
def nonemptyFiberRecordCount : ℕ :=
  (sixQubitModuli.map fun q =>
    ((logicalOrders q).map fun m => nonemptyFiberPairCount q m).sum).sum

/-- The streaming count is definitionally tied to the explicit surviving
enumeration; this prevents a separately transcribed count from going green. -/
theorem nonemptyFiberRecords_length_eq_count :
    nonemptyFiberRecords.length = nonemptyFiberRecordCount := by
  simp [nonemptyFiberRecords, nonemptyFiberRecordCount, nonemptyFiberPairCount,
    List.length_flatMap]

/- The final count is checked below in bounded `(q,m,a₀)` chunks.  Each leaf
theorem reduces an actual `nonemptyAngleChunk`; the pair and global totals are
then obtained only by adding those checked leaves. -/

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_3_0 :
    (nonemptyAngleChunk 9 3 0).length = 1118 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_2_2_0 :
    (nonemptyAngleChunk 2 2 0).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_2_2_1 :
    (nonemptyAngleChunk 2 2 1).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_3_3_0 :
    (nonemptyAngleChunk 3 3 0).length = 19 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_3_3_1 :
    (nonemptyAngleChunk 3 3 1).length = 6 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_3_3_2 :
    (nonemptyAngleChunk 3 3 2).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_4_2_0 :
    (nonemptyAngleChunk 4 2 0).length = 47 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_4_2_1 :
    (nonemptyAngleChunk 4 2 1).length = 21 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_4_2_2 :
    (nonemptyAngleChunk 4 2 2).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_4_2_3 :
    (nonemptyAngleChunk 4 2 3).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_4_4_0 :
    (nonemptyAngleChunk 4 4 0).length = 48 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_4_4_1 :
    (nonemptyAngleChunk 4 4 1).length = 21 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_4_4_2 :
    (nonemptyAngleChunk 4 4 2).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_4_4_3 :
    (nonemptyAngleChunk 4 4 3).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_5_5_0 :
    (nonemptyAngleChunk 5 5 0).length = 116 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_5_5_1 :
    (nonemptyAngleChunk 5 5 1).length = 56 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_5_5_2 :
    (nonemptyAngleChunk 5 5 2).length = 21 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_5_5_3 :
    (nonemptyAngleChunk 5 5 3).length = 6 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_5_5_4 :
    (nonemptyAngleChunk 5 5 4).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_2_0 :
    (nonemptyAngleChunk 6 2 0).length = 214 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_2_1 :
    (nonemptyAngleChunk 6 2 1).length = 126 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_2_2 :
    (nonemptyAngleChunk 6 2 2).length = 50 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_2_3 :
    (nonemptyAngleChunk 6 2 3).length = 20 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_2_4 :
    (nonemptyAngleChunk 6 2 4).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_2_5 :
    (nonemptyAngleChunk 6 2 5).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_3_0 :
    (nonemptyAngleChunk 6 3 0).length = 208 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_3_1 :
    (nonemptyAngleChunk 6 3 1).length = 125 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_3_2 :
    (nonemptyAngleChunk 6 3 2).length = 50 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_3_3 :
    (nonemptyAngleChunk 6 3 3).length = 19 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_3_4 :
    (nonemptyAngleChunk 6 3 4).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_3_5 :
    (nonemptyAngleChunk 6 3 5).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_6_0 :
    (nonemptyAngleChunk 6 6 0).length = 212 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_6_1 :
    (nonemptyAngleChunk 6 6 1).length = 126 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_6_2 :
    (nonemptyAngleChunk 6 6 2).length = 49 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_6_3 :
    (nonemptyAngleChunk 6 6 3).length = 19 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_6_4 :
    (nonemptyAngleChunk 6 6 4).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_6_6_5 :
    (nonemptyAngleChunk 6 6 5).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_7_7_0 :
    (nonemptyAngleChunk 7 7 0).length = 417 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_7_7_1 :
    (nonemptyAngleChunk 7 7 1).length = 252 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_7_7_2 :
    (nonemptyAngleChunk 7 7 2).length = 126 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_7_7_3 :
    (nonemptyAngleChunk 7 7 3).length = 56 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_7_7_4 :
    (nonemptyAngleChunk 7 7 4).length = 21 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_7_7_5 :
    (nonemptyAngleChunk 7 7 5).length = 6 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_7_7_6 :
    (nonemptyAngleChunk 7 7 6).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_2_0 :
    (nonemptyAngleChunk 8 2 0).length = 662 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_2_1 :
    (nonemptyAngleChunk 8 2 1).length = 461 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_2_2 :
    (nonemptyAngleChunk 8 2 2).length = 231 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_2_3 :
    (nonemptyAngleChunk 8 2 3).length = 125 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_2_4 :
    (nonemptyAngleChunk 8 2 4).length = 50 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_2_5 :
    (nonemptyAngleChunk 8 2 5).length = 21 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_2_6 :
    (nonemptyAngleChunk 8 2 6).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_2_7 :
    (nonemptyAngleChunk 8 2 7).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_4_0 :
    (nonemptyAngleChunk 8 4 0).length = 658 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_4_1 :
    (nonemptyAngleChunk 8 4 1).length = 458 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_4_2 :
    (nonemptyAngleChunk 8 4 2).length = 231 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_4_3 :
    (nonemptyAngleChunk 8 4 3).length = 123 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_4_4 :
    (nonemptyAngleChunk 8 4 4).length = 47 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_4_5 :
    (nonemptyAngleChunk 8 4 5).length = 21 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_4_6 :
    (nonemptyAngleChunk 8 4 6).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_4_7 :
    (nonemptyAngleChunk 8 4 7).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_8_0 :
    (nonemptyAngleChunk 8 8 0).length = 671 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_8_1 :
    (nonemptyAngleChunk 8 8 1).length = 462 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_8_2 :
    (nonemptyAngleChunk 8 8 2).length = 231 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_8_3 :
    (nonemptyAngleChunk 8 8 3).length = 122 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_8_4 :
    (nonemptyAngleChunk 8 8 4).length = 48 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_8_5 :
    (nonemptyAngleChunk 8 8 5).length = 21 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_8_6 :
    (nonemptyAngleChunk 8 8 6).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_8_8_7 :
    (nonemptyAngleChunk 8 8 7).length = 0 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_3_1 :
    (nonemptyAngleChunk 9 3 1).length = 788 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_3_2 :
    (nonemptyAngleChunk 9 3 2).length = 457 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_3_3 :
    (nonemptyAngleChunk 9 3 3).length = 246 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_3_4 :
    (nonemptyAngleChunk 9 3 4).length = 124 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_3_5 :
    (nonemptyAngleChunk 9 3 5).length = 55 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_3_6 :
    (nonemptyAngleChunk 9 3 6).length = 20 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_3_7 :
    (nonemptyAngleChunk 9 3 7).length = 6 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_3_8 :
    (nonemptyAngleChunk 9 3 8).length = 1 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_9_0 :
    (nonemptyAngleChunk 9 9 0).length = 1115 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_9_1 :
    (nonemptyAngleChunk 9 9 1).length = 792 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_9_2 :
    (nonemptyAngleChunk 9 9 2).length = 452 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_9_3 :
    (nonemptyAngleChunk 9 9 3).length = 236 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_9_4 :
    (nonemptyAngleChunk 9 9 4).length = 123 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_9_5 :
    (nonemptyAngleChunk 9 9 5).length = 55 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_9_6 :
    (nonemptyAngleChunk 9 9 6).length = 19 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_9_7 :
    (nonemptyAngleChunk 9 9 7).length = 5 := by decide

set_option maxRecDepth 1000000 in
theorem nonempty_chunk_9_9_8 :
    (nonemptyAngleChunk 9 9 8).length = 0 := by decide

theorem nonempty_pair_2_2 : nonemptyFiberPairCount 2 2 = 6 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 2 = [0, 1] by decide]
  norm_num [
      nonempty_chunk_2_2_0,
      nonempty_chunk_2_2_1]

theorem nonempty_pair_3_3 : nonemptyFiberPairCount 3 3 = 26 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 3 = [0, 1, 2] by decide]
  norm_num [
      nonempty_chunk_3_3_0,
      nonempty_chunk_3_3_1,
      nonempty_chunk_3_3_2]

theorem nonempty_pair_4_2 : nonemptyFiberPairCount 4 2 = 74 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 4 = [0, 1, 2, 3] by decide]
  norm_num [
      nonempty_chunk_4_2_0,
      nonempty_chunk_4_2_1,
      nonempty_chunk_4_2_2,
      nonempty_chunk_4_2_3]

theorem nonempty_pair_4_4 : nonemptyFiberPairCount 4 4 = 75 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 4 = [0, 1, 2, 3] by decide]
  norm_num [
      nonempty_chunk_4_4_0,
      nonempty_chunk_4_4_1,
      nonempty_chunk_4_4_2,
      nonempty_chunk_4_4_3]

theorem nonempty_pair_5_5 : nonemptyFiberPairCount 5 5 = 200 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 5 = [0, 1, 2, 3, 4] by decide]
  norm_num [
      nonempty_chunk_5_5_0,
      nonempty_chunk_5_5_1,
      nonempty_chunk_5_5_2,
      nonempty_chunk_5_5_3,
      nonempty_chunk_5_5_4]

theorem nonempty_pair_6_2 : nonemptyFiberPairCount 6 2 = 416 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] by decide]
  norm_num [
      nonempty_chunk_6_2_0,
      nonempty_chunk_6_2_1,
      nonempty_chunk_6_2_2,
      nonempty_chunk_6_2_3,
      nonempty_chunk_6_2_4,
      nonempty_chunk_6_2_5]

theorem nonempty_pair_6_3 : nonemptyFiberPairCount 6 3 = 408 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] by decide]
  norm_num [
      nonempty_chunk_6_3_0,
      nonempty_chunk_6_3_1,
      nonempty_chunk_6_3_2,
      nonempty_chunk_6_3_3,
      nonempty_chunk_6_3_4,
      nonempty_chunk_6_3_5]

theorem nonempty_pair_6_6 : nonemptyFiberPairCount 6 6 = 412 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 6 = [0, 1, 2, 3, 4, 5] by decide]
  norm_num [
      nonempty_chunk_6_6_0,
      nonempty_chunk_6_6_1,
      nonempty_chunk_6_6_2,
      nonempty_chunk_6_6_3,
      nonempty_chunk_6_6_4,
      nonempty_chunk_6_6_5]

theorem nonempty_pair_7_7 : nonemptyFiberPairCount 7 7 = 879 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 7 = [0, 1, 2, 3, 4, 5, 6] by decide]
  norm_num [
      nonempty_chunk_7_7_0,
      nonempty_chunk_7_7_1,
      nonempty_chunk_7_7_2,
      nonempty_chunk_7_7_3,
      nonempty_chunk_7_7_4,
      nonempty_chunk_7_7_5,
      nonempty_chunk_7_7_6]

theorem nonempty_pair_8_2 : nonemptyFiberPairCount 8 2 = 1556 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] by decide]
  norm_num [
      nonempty_chunk_8_2_0,
      nonempty_chunk_8_2_1,
      nonempty_chunk_8_2_2,
      nonempty_chunk_8_2_3,
      nonempty_chunk_8_2_4,
      nonempty_chunk_8_2_5,
      nonempty_chunk_8_2_6,
      nonempty_chunk_8_2_7]

theorem nonempty_pair_8_4 : nonemptyFiberPairCount 8 4 = 1544 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] by decide]
  norm_num [
      nonempty_chunk_8_4_0,
      nonempty_chunk_8_4_1,
      nonempty_chunk_8_4_2,
      nonempty_chunk_8_4_3,
      nonempty_chunk_8_4_4,
      nonempty_chunk_8_4_5,
      nonempty_chunk_8_4_6,
      nonempty_chunk_8_4_7]

theorem nonempty_pair_8_8 : nonemptyFiberPairCount 8 8 = 1560 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] by decide]
  norm_num [
      nonempty_chunk_8_8_0,
      nonempty_chunk_8_8_1,
      nonempty_chunk_8_8_2,
      nonempty_chunk_8_8_3,
      nonempty_chunk_8_8_4,
      nonempty_chunk_8_8_5,
      nonempty_chunk_8_8_6,
      nonempty_chunk_8_8_7]

theorem nonempty_pair_9_3 : nonemptyFiberPairCount 9 3 = 2815 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] by decide]
  norm_num [
      nonempty_chunk_9_3_0,
      nonempty_chunk_9_3_1,
      nonempty_chunk_9_3_2,
      nonempty_chunk_9_3_3,
      nonempty_chunk_9_3_4,
      nonempty_chunk_9_3_5,
      nonempty_chunk_9_3_6,
      nonempty_chunk_9_3_7,
      nonempty_chunk_9_3_8]

theorem nonempty_pair_9_9 : nonemptyFiberPairCount 9 9 = 2797 := by
  unfold nonemptyFiberPairCount
  rw [show List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] by decide]
  norm_num [
      nonempty_chunk_9_9_0,
      nonempty_chunk_9_9_1,
      nonempty_chunk_9_9_2,
      nonempty_chunk_9_9_3,
      nonempty_chunk_9_9_4,
      nonempty_chunk_9_9_5,
      nonempty_chunk_9_9_6,
      nonempty_chunk_9_9_7,
      nonempty_chunk_9_9_8]

/-- Equation `six:eq:nonemptyrecords`: the exact outer enumeration has
`12,768` records after the nonempty-second-fiber test.  The proof term is a
short arithmetic combination of the bounded chunk theorems above. -/
theorem nonempty_fiber_record_count : nonemptyFiberRecordCount = 12768 := by
  norm_num [nonemptyFiberRecordCount, sixQubitModuli, logicalOrders,
    List.range', List.range,
    nonempty_pair_2_2, nonempty_pair_3_3,
    nonempty_pair_4_2, nonempty_pair_4_4, nonempty_pair_5_5,
    nonempty_pair_6_2, nonempty_pair_6_3, nonempty_pair_6_6,
    nonempty_pair_7_7,
    nonempty_pair_8_2, nonempty_pair_8_4, nonempty_pair_8_8,
    nonempty_pair_9_3, nonempty_pair_9_9]

/-- The explicit surviving list therefore has length `12,768`. -/
theorem nonempty_fiber_records_exact : nonemptyFiberRecords.length = 12768 :=
  nonemptyFiberRecords_length_eq_count.trans nonempty_fiber_record_count


end MainTheory.OuterEnumeration
