import MainTheory.OuterEnumeration
import MainTheory.Gate
import MainTheory.Normalize
import MainTheory.FinitePipeline

/-!
# Semantic completeness bridges for the outer enumeration

This module connects the executable six-coordinate enumeration to the
mathematical predicates used elsewhere in the development.  In particular,
the masks constructed below are computed from the residue predicate itself;
they are not separately transcribed data.
-/

namespace MainTheory.OuterCompleteness

open scoped BigOperators
open MainTheory

/-! ## Completeness of the sorted six-angle enumeration -/

/-- The mathematical specification of a canonical angle representative. -/
def IsCanonicalAngle6 (q : ℕ) (a : OuterEnumeration.Angle6) : Prop :=
  (∀ i, a i < q) ∧ Monotone a

theorem mem_range'_one_iff {lo count value : ℕ} :
    value ∈ List.range' lo count ↔ lo ≤ value ∧ value < lo + count := by
  constructor
  · intro h
    rcases List.mem_range'.mp h with ⟨i, hi, hvalue⟩
    constructor <;> omega
  · rintro ⟨hlower, hupper⟩
    apply List.mem_range'.mpr
    exact ⟨value - lo, by omega, by omega⟩

/-- Every tuple emitted by `weakAngles6` is in range and weakly increasing. -/
theorem mem_weakAngles6_implies_canonical {q : ℕ}
    {a : OuterEnumeration.Angle6}
    (ha : a ∈ OuterEnumeration.weakAngles6 q) : IsCanonicalAngle6 q a := by
  simp only [OuterEnumeration.weakAngles6,
    OuterEnumeration.weakAngles6FromFirst, List.mem_flatMap, List.mem_map,
    List.mem_range, mem_range'_one_iff] at ha
  rcases ha with
    ⟨a0, ha0, a1, ha1, a2, ha2, a3, ha3, a4, ha4, a5, ha5, rfl⟩
  constructor
  · intro i
    fin_cases i <;> simp [OuterEnumeration.angle6] <;> omega
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [OuterEnumeration.angle6] at hij ⊢ <;> omega

/-- Conversely, every in-range weakly increasing six-tuple occurs in the
nested range generator. -/
theorem canonical_mem_weakAngles6 {q : ℕ} {a : OuterEnumeration.Angle6}
    (ha : IsCanonicalAngle6 q a) : a ∈ OuterEnumeration.weakAngles6 q := by
  rcases ha with ⟨hrange, hmono⟩
  simp only [OuterEnumeration.weakAngles6,
    OuterEnumeration.weakAngles6FromFirst, List.mem_flatMap, List.mem_map,
    List.mem_range, mem_range'_one_iff]
  refine ⟨a 0, hrange 0, a 1, ?_, a 2, ?_, a 3, ?_, a 4, ?_, a 5, ?_, ?_⟩
  · constructor
    · exact hmono (show (0 : Fin 6) ≤ 1 by decide)
    · have := hrange 0
      have := hrange 1
      omega
  · constructor
    · exact hmono (show (1 : Fin 6) ≤ 2 by decide)
    · have := hrange 1
      have := hrange 2
      omega
  · constructor
    · exact hmono (show (2 : Fin 6) ≤ 3 by decide)
    · have := hrange 2
      have := hrange 3
      omega
  · constructor
    · exact hmono (show (3 : Fin 6) ≤ 4 by decide)
    · have := hrange 3
      have := hrange 4
      omega
  · constructor
    · exact hmono (show (4 : Fin 6) ≤ 5 by decide)
    · have := hrange 4
      have := hrange 5
      omega
  · apply funext
    intro i
    fin_cases i <;> rfl

/-- Exact soundness-and-completeness specification for `weakAngles6`. -/
theorem mem_weakAngles6_iff {q : ℕ} {a : OuterEnumeration.Angle6} :
    a ∈ OuterEnumeration.weakAngles6 q ↔ IsCanonicalAngle6 q a :=
  ⟨mem_weakAngles6_implies_canonical, canonical_mem_weakAngles6⟩

/-- Sorting coordinates gives a representative that the generator actually
enumerates; the exhibited map is a genuine coordinate permutation. -/
theorem exists_permutation_mem_weakAngles6 {q : ℕ}
    (a : OuterEnumeration.Angle6) (ha : ∀ i, a i < q) :
    ∃ σ : Equiv.Perm (Fin 6),
      (a ∘ σ) ∈ OuterEnumeration.weakAngles6 q := by
  refine ⟨Tuple.sort a, canonical_mem_weakAngles6 ?_⟩
  exact ⟨fun i => ha (Tuple.sort a i), Tuple.monotone_sort a⟩

private def tail5 (q a0 a1 a2 a3 a4 : ℕ) :
    List OuterEnumeration.Angle6 :=
  (List.range' a4 (q - a4)).map fun a5 =>
    OuterEnumeration.angle6 a0 a1 a2 a3 a4 a5

private def tail4 (q a0 a1 a2 a3 : ℕ) :
    List OuterEnumeration.Angle6 :=
  (List.range' a3 (q - a3)).flatMap fun a4 =>
    tail5 q a0 a1 a2 a3 a4

private def tail3 (q a0 a1 a2 : ℕ) :
    List OuterEnumeration.Angle6 :=
  (List.range' a2 (q - a2)).flatMap fun a3 =>
    tail4 q a0 a1 a2 a3

private def tail2 (q a0 a1 : ℕ) : List OuterEnumeration.Angle6 :=
  (List.range' a1 (q - a1)).flatMap fun a2 => tail3 q a0 a1 a2

private def tail1 (q a0 : ℕ) : List OuterEnumeration.Angle6 :=
  (List.range' a0 (q - a0)).flatMap fun a1 => tail2 q a0 a1

private theorem nodup_flatMap_of_tag {alpha beta : Type*}
    (values : List alpha) (f : alpha → List beta) (tag : beta → alpha)
    (hvalues : values.Nodup)
    (hf : ∀ value ∈ values, (f value).Nodup)
    (htag : ∀ value ∈ values, ∀ item ∈ f value, tag item = value) :
    (values.flatMap f).Nodup := by
  rw [List.nodup_flatMap]
  refine ⟨hf, ?_⟩
  apply hvalues.pairwise_of_forall_ne
  intro x hx y hy hxy
  change List.Disjoint (f x) (f y)
  rw [List.disjoint_left]
  intro z hzx hzy
  apply hxy
  exact (htag x hx z hzx).symm.trans (htag y hy z hzy)

private theorem tail5_nodup (q a0 a1 a2 a3 a4 : ℕ) :
    (tail5 q a0 a1 a2 a3 a4).Nodup := by
  apply List.Nodup.map
  · intro x y hxy
    have h := congrFun hxy 5
    simpa [OuterEnumeration.angle6] using h
  · exact List.nodup_range'

private theorem tail4_nodup (q a0 a1 a2 a3 : ℕ) :
    (tail4 q a0 a1 a2 a3).Nodup := by
  apply nodup_flatMap_of_tag _ _ (fun a => a 4) List.nodup_range'
  · intro a4 _
    exact tail5_nodup q a0 a1 a2 a3 a4
  · intro a4 _ item hitem
    simp only [tail5, List.mem_map] at hitem
    rcases hitem with ⟨a5, _, rfl⟩
    rfl

private theorem tail3_nodup (q a0 a1 a2 : ℕ) :
    (tail3 q a0 a1 a2).Nodup := by
  apply nodup_flatMap_of_tag _ _ (fun a => a 3) List.nodup_range'
  · intro a3 _
    exact tail4_nodup q a0 a1 a2 a3
  · intro a3 _ item hitem
    simp only [tail4, List.mem_flatMap] at hitem
    rcases hitem with ⟨a4, _, hitem⟩
    simp only [tail5, List.mem_map] at hitem
    rcases hitem with ⟨a5, _, rfl⟩
    rfl

private theorem tail2_nodup (q a0 a1 : ℕ) :
    (tail2 q a0 a1).Nodup := by
  apply nodup_flatMap_of_tag _ _ (fun a => a 2) List.nodup_range'
  · intro a2 _
    exact tail3_nodup q a0 a1 a2
  · intro a2 _ item hitem
    simp only [tail3, List.mem_flatMap] at hitem
    rcases hitem with ⟨a3, _, hitem⟩
    simp only [tail4, List.mem_flatMap] at hitem
    rcases hitem with ⟨a4, _, hitem⟩
    simp only [tail5, List.mem_map] at hitem
    rcases hitem with ⟨a5, _, rfl⟩
    rfl

private theorem tail1_nodup (q a0 : ℕ) :
    (tail1 q a0).Nodup := by
  apply nodup_flatMap_of_tag _ _ (fun a => a 1) List.nodup_range'
  · intro a1 _
    exact tail2_nodup q a0 a1
  · intro a1 _ item hitem
    simp only [tail2, List.mem_flatMap] at hitem
    rcases hitem with ⟨a2, _, hitem⟩
    simp only [tail3, List.mem_flatMap] at hitem
    rcases hitem with ⟨a3, _, hitem⟩
    simp only [tail4, List.mem_flatMap] at hitem
    rcases hitem with ⟨a4, _, hitem⟩
    simp only [tail5, List.mem_map] at hitem
    rcases hitem with ⟨a5, _, rfl⟩
    rfl

/-- `weakAngles6` never emits the same canonical representative twice. -/
theorem weakAngles6_nodup (q : ℕ) :
    (OuterEnumeration.weakAngles6 q).Nodup := by
  have h : ((List.range q).flatMap (tail1 q)).Nodup := by
    apply nodup_flatMap_of_tag _ _ (fun a => a 0) List.nodup_range
    · intro a0 _
      exact tail1_nodup q a0
    · intro a0 _ item hitem
      simp only [tail1, List.mem_flatMap] at hitem
      rcases hitem with ⟨a1, _, hitem⟩
      simp only [tail2, List.mem_flatMap] at hitem
      rcases hitem with ⟨a2, _, hitem⟩
      simp only [tail3, List.mem_flatMap] at hitem
      rcases hitem with ⟨a3, _, hitem⟩
      simp only [tail4, List.mem_flatMap] at hitem
      rcases hitem with ⟨a4, _, hitem⟩
      simp only [tail5, List.mem_map] at hitem
      rcases hitem with ⟨a5, _, rfl⟩
      rfl
  simpa [OuterEnumeration.weakAngles6,
    OuterEnumeration.weakAngles6FromFirst, tail1, tail2, tail3, tail4, tail5]
    using h

/-! ## Primitivity -/

/-- Splitting the nested gcd says exactly that a divisor divides the modulus
and all six entries. -/
theorem dvd_angleGCD_iff {q d : ℕ} {a : OuterEnumeration.Angle6} :
    d ∣ OuterEnumeration.angleGCD q a ↔ d ∣ q ∧ ∀ i, d ∣ a i := by
  simp only [OuterEnumeration.angleGCD, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨hdq, h0, h1, h2, h3, h4, h5⟩
    refine ⟨hdq, fun i ↦ ?_⟩
    fin_cases i <;> assumption
  · rintro ⟨hdq, hda⟩
    exact ⟨hdq, hda 0, hda 1, hda 2, hda 3, hda 4, hda 5⟩

/-- The executable nested-gcd criterion and `Gate.Primitive` are the same
criterion.  The range hypothesis is what identifies the value of a natural
cast into `ZMod q` with the original representative. -/
theorem angleGCD_eq_one_iff_gatePrimitive {q : ℕ} (_hq : 0 < q)
    (a : OuterEnumeration.Angle6) (ha : ∀ i, a i < q) :
    OuterEnumeration.angleGCD q a = 1 ↔
      Gate.Primitive q (fun i ↦ (a i : ZMod q)) := by
  letI : NeZero q := ⟨Nat.ne_of_gt _hq⟩
  constructor
  · intro hg d hdq hda
    have hdai : ∀ i, d ∣ a i := by
      intro i
      simpa [ZMod.val_natCast_of_lt (ha i)] using hda i
    have hdg : d ∣ OuterEnumeration.angleGCD q a :=
      (dvd_angleGCD_iff).2 ⟨hdq, hdai⟩
    rw [hg] at hdg
    exact Nat.dvd_one.mp hdg
  · intro hp
    let d := OuterEnumeration.angleGCD q a
    have hd : d ∣ q ∧ ∀ i, d ∣ a i :=
      (dvd_angleGCD_iff).1 (dvd_refl d)
    apply hp d hd.1
    intro i
    simpa [ZMod.val_natCast_of_lt (ha i)] using hd.2 i

/-- Boolean form used by `primitiveAngles6`. -/
theorem isPrimitive_iff_gatePrimitive {q : ℕ} (hq : 0 < q)
    (a : OuterEnumeration.Angle6) (ha : ∀ i, a i < q) :
    OuterEnumeration.IsPrimitive q a = true ↔
      Gate.Primitive q (fun i ↦ (a i : ZMod q)) := by
  rw [← angleGCD_eq_one_iff_gatePrimitive hq a ha]
  simp [OuterEnumeration.IsPrimitive]

/-! ## Exact 64-bit residue masks -/

/-- Pack a low-to-high list of Boolean bits into a natural number. -/
def packBits : List Bool → ℕ
  | [] => 0
  | b :: bs => Nat.bit b (packBits bs)

@[simp] theorem packBits_nil : packBits [] = 0 := rfl

@[simp] theorem packBits_cons (b : Bool) (bs : List Bool) :
    packBits (b :: bs) = Nat.bit b (packBits bs) := rfl

/-- Every in-range bit of `packBits` is the corresponding input bit. -/
theorem packBits_testBit {bs : List Bool} {i : ℕ} (hi : i < bs.length) :
    (packBits bs).testBit i = bs[i] := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero => simp [packBits]
      | succ i =>
          simpa [packBits, Nat.testBit_bit_succ] using
            ih (Nat.lt_of_succ_lt_succ hi)

/-- Pack an arbitrary Boolean predicate on the 64 six-bit words. -/
def maskOfPredicate (P : FinitePipeline.Word6 → Bool) : ℕ :=
  packBits (List.ofFn P)

/-- `maskOfPredicate` has exactly the requested low 64 bits. -/
theorem maskOfPredicate_testBit (P : FinitePipeline.Word6 → Bool)
    (x : FinitePipeline.Word6) :
    (maskOfPredicate P).testBit x.1 = P x := by
  unfold maskOfPredicate
  rw [packBits_testBit (by simp)]
  change (List.ofFn P).get ⟨x.1, by simp⟩ = P x
  simpa using List.get_ofFn P ⟨x.1, by simp⟩

/-- The actual mask of the natural residue fiber `residue`. -/
def residueMask (r : OuterEnumeration.RawRecord) (residue : ℕ) : ℕ :=
  maskOfPredicate fun x =>
    decide (OuterEnumeration.subsetSum r.a x.1 % r.q = residue)

/-- The finite-pipeline pair computed from the two normalized residue fibers. -/
def recordFiberPair (r : OuterEnumeration.RawRecord) : FinitePipeline.FiberPair where
  q := r.q
  m := r.m
  mask0 := residueMask r 0
  mask1 := residueMask r (r.q / r.m)

theorem recordFiberPair_q (r : OuterEnumeration.RawRecord) :
    (recordFiberPair r).q = r.q := rfl

theorem recordFiberPair_m (r : OuterEnumeration.RawRecord) :
    (recordFiberPair r).m = r.m := rfl

/-- A bit is set exactly when that word belongs to the requested natural
residue fiber. -/
theorem residueMask_testBit_iff (r : OuterEnumeration.RawRecord) (residue : ℕ)
    (x : FinitePipeline.Word6) :
    (residueMask r residue).testBit x.1 = true ↔
      OuterEnumeration.subsetSum r.a x.1 % r.q = residue := by
  rw [residueMask, maskOfPredicate_testBit]
  simp

/-- The first mask of `recordFiberPair` is exactly the zero-residue fiber. -/
theorem in_recordFiberPair_mask0_iff (r : OuterEnumeration.RawRecord)
    (x : FinitePipeline.Word6) :
    FinitePipeline.InMask (recordFiberPair r).mask0 x ↔
      OuterEnumeration.subsetSum r.a x.1 % r.q = 0 := by
  exact residueMask_testBit_iff r 0 x

/-- The second mask of `recordFiberPair` is exactly the normalized logical
residue fiber. -/
theorem in_recordFiberPair_mask1_iff (r : OuterEnumeration.RawRecord)
    (x : FinitePipeline.Word6) :
    FinitePipeline.InMask (recordFiberPair r).mask1 x ↔
      OuterEnumeration.subsetSum r.a x.1 % r.q = r.q / r.m := by
  exact residueMask_testBit_iff r (r.q / r.m) x

/-- The residue fiber as an actual finite set of the 64 Boolean words. -/
def residueFiber (r : OuterEnumeration.RawRecord) (residue : ℕ) :
    Finset FinitePipeline.Word6 :=
  Finset.univ.filter fun x => OuterEnumeration.subsetSum r.a x.1 % r.q = residue

@[simp] theorem mem_residueFiber_iff (r : OuterEnumeration.RawRecord) (residue : ℕ)
    (x : FinitePipeline.Word6) :
    x ∈ residueFiber r residue ↔
      OuterEnumeration.subsetSum r.a x.1 % r.q = residue := by
  simp [residueFiber]

theorem in_recordFiberPair_mask0_iff_mem (r : OuterEnumeration.RawRecord)
    (x : FinitePipeline.Word6) :
    FinitePipeline.InMask (recordFiberPair r).mask0 x ↔
      x ∈ residueFiber r 0 := by
  rw [in_recordFiberPair_mask0_iff, mem_residueFiber_iff]

theorem in_recordFiberPair_mask1_iff_mem (r : OuterEnumeration.RawRecord)
    (x : FinitePipeline.Word6) :
    FinitePipeline.InMask (recordFiberPair r).mask1 x ↔
      x ∈ residueFiber r (r.q / r.m) := by
  rw [in_recordFiberPair_mask1_iff, mem_residueFiber_iff]

/-! ## The two executable nonemptiness tests -/

/-- Raw (not yet reduced modulo `q`) subset-sum semantics. -/
def IsRawSubsetSum : List ℕ → ℕ → Prop
  | [], target => target = 0
  | value :: rest, target =>
      IsRawSubsetSum rest target ∨
        ∃ subtotal, IsRawSubsetSum rest subtotal ∧ target = value + subtotal

/-- Sum selected by a low-to-high Boolean list.  The semantic theorems below
always require the choice list to have the same length as the value list. -/
def choiceSum : List ℕ → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | value :: rest, choose :: choices =>
      (if choose then value else 0) + choiceSum rest choices

/-- `IsRawSubsetSum` has no hidden witnesses: it is exactly a Boolean choice
at each position. -/
theorem isRawSubsetSum_iff_exists_choice (values : List ℕ) (target : ℕ) :
    IsRawSubsetSum values target ↔
      ∃ choices : List Bool,
        choices.length = values.length ∧ choiceSum values choices = target := by
  induction values generalizing target with
  | nil =>
      constructor
      · intro h
        exact ⟨[], rfl, h.symm⟩
      · rintro ⟨choices, hlength, hsum⟩
        have : choices = [] := List.eq_nil_of_length_eq_zero hlength
        subst choices
        simpa [IsRawSubsetSum, choiceSum] using hsum.symm
  | cons value rest ih =>
      constructor
      · intro h
        rcases h with hold | ⟨subtotal, hsubtotal, rfl⟩
        · rcases (ih target).1 hold with ⟨choices, hlength, hsum⟩
          exact ⟨false :: choices, by simp [hlength], by simpa [choiceSum] using hsum⟩
        · rcases (ih subtotal).1 hsubtotal with ⟨choices, hlength, hsum⟩
          exact ⟨true :: choices, by simp [hlength], by simp [choiceSum, hsum]⟩
      · rintro ⟨choices, hlength, hsum⟩
        cases choices with
        | nil => simp at hlength
        | cons choose choices =>
            have htail : choices.length = rest.length := by simpa using hlength
            cases choose with
            | false =>
                apply Or.inl
                apply (ih _).2
                exact ⟨choices, htail, by simpa [choiceSum] using hsum⟩
            | true =>
                refine Or.inr ⟨choiceSum rest choices,
                  (ih _).2 ⟨choices, htail, rfl⟩, ?_⟩
                simpa [choiceSum] using hsum.symm

/-- The inductive evaluator is a modulo reduction of a genuine raw subset
sum.  This holds even at `q = 0`, matching Lean's natural-number `% 0`
semantics. -/
theorem mem_reachableResidues_iff_exists_raw (q target : ℕ) (values : List ℕ) :
    target ∈ OuterEnumeration.reachableResidues q values ↔
      ∃ raw, IsRawSubsetSum values raw ∧ raw % q = target := by
  induction values generalizing target with
  | nil =>
      simp [OuterEnumeration.reachableResidues, IsRawSubsetSum, eq_comm]
  | cons value rest ih =>
      simp only [OuterEnumeration.reachableResidues, List.mem_append,
        List.mem_map]
      constructor
      · rintro (hold | ⟨residue, hresidue, rfl⟩)
        · rcases (ih target).1 hold with ⟨raw, hraw, hmod⟩
          exact ⟨raw, Or.inl hraw, hmod⟩
        · rcases (ih residue).1 hresidue with ⟨raw, hraw, hmod⟩
          refine ⟨value + raw, Or.inr ⟨raw, hraw, rfl⟩, ?_⟩
          simp [Nat.add_mod, hmod]
      · rintro ⟨raw, hraw, hmod⟩
        rcases hraw with hold | ⟨subtotal, hsubtotal, rfl⟩
        · exact Or.inl ((ih target).2 ⟨raw, hold, hmod⟩)
        · refine Or.inr ⟨subtotal % q, (ih _).2 ⟨subtotal, hsubtotal, rfl⟩, ?_⟩
          simpa [Nat.add_mod] using hmod

/-- Reachability is equivalently one Boolean selector per input entry. -/
theorem mem_reachableResidues_iff_exists_choice (q target : ℕ)
    (values : List ℕ) :
    target ∈ OuterEnumeration.reachableResidues q values ↔
      ∃ choices : List Bool, choices.length = values.length ∧
        choiceSum values choices % q = target := by
  rw [mem_reachableResidues_iff_exists_raw]
  constructor
  · rintro ⟨raw, hraw, hmod⟩
    rcases (isRawSubsetSum_iff_exists_choice values raw).1 hraw with
      ⟨choices, hlength, rfl⟩
    exact ⟨choices, hlength, hmod⟩
  · rintro ⟨choices, hlength, hchoose⟩
    exact ⟨choiceSum values choices,
      (isRawSubsetSum_iff_exists_choice values _).2
        ⟨choices, hlength, rfl⟩,
      hchoose⟩

theorem packBits_lt_two_pow_length (bs : List Bool) :
    packBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      cases b <;> simp [packBits, Nat.bit, pow_succ] <;> omega

/-- A residue mask has no bits at positions 64 or above. -/
theorem residueMask_lt_two_pow_64 (r : OuterEnumeration.RawRecord)
    (residue : ℕ) : residueMask r residue < 2 ^ 64 := by
  unfold residueMask maskOfPredicate
  simpa using packBits_lt_two_pow_length
    (List.ofFn fun x : FinitePipeline.Word6 =>
      decide (OuterEnumeration.subsetSum r.a x.1 % r.q = residue))

theorem recordFiberPair_mask0_lt_two_pow_64 (r : OuterEnumeration.RawRecord) :
    (recordFiberPair r).mask0 < 2 ^ 64 :=
  residueMask_lt_two_pow_64 r 0

theorem recordFiberPair_mask1_lt_two_pow_64 (r : OuterEnumeration.RawRecord) :
    (recordFiberPair r).mask1 < 2 ^ 64 :=
  residueMask_lt_two_pow_64 r (r.q / r.m)

/-- A six-choice list, packed low-bit first, has exactly the same selected sum
as the direct mask implementation. -/
theorem subsetSum_packBits_of_length_six (a : OuterEnumeration.Angle6)
    (choices : List Bool) (hlength : choices.length = 6) :
    OuterEnumeration.subsetSum a (packBits choices) =
      choiceSum [a 0, a 1, a 2, a 3, a 4, a 5] choices := by
  rcases choices with _ | ⟨b0, choices⟩
  · simp at hlength
  rcases choices with _ | ⟨b1, choices⟩
  · simp at hlength
  rcases choices with _ | ⟨b2, choices⟩
  · simp at hlength
  rcases choices with _ | ⟨b3, choices⟩
  · simp at hlength
  rcases choices with _ | ⟨b4, choices⟩
  · simp at hlength
  rcases choices with _ | ⟨b5, choices⟩
  · simp at hlength
  have : choices = [] := List.eq_nil_of_length_eq_zero (by simpa using hlength)
  subst choices
  simp [OuterEnumeration.subsetSum, choiceSum, packBits,
    Nat.testBit_bit_succ, Nat.add_assoc]

/-- Reading the six low bits of a word and summing them agrees with
`subsetSum`. -/
theorem choiceSum_wordBits (a : OuterEnumeration.Angle6)
    (x : FinitePipeline.Word6) :
    choiceSum [a 0, a 1, a 2, a 3, a 4, a 5]
      [x.1.testBit 0, x.1.testBit 1, x.1.testBit 2,
       x.1.testBit 3, x.1.testBit 4, x.1.testBit 5] =
      OuterEnumeration.subsetSum a x.1 := by
  simp [OuterEnumeration.subsetSum, choiceSum, Nat.add_assoc]

/-- For six entries, the mathematical Boolean-choice witness is exactly one
of the 64 encoded words. -/
theorem mem_reachableResidues_six_iff_word (q target : ℕ)
    (a : OuterEnumeration.Angle6) :
    target ∈ OuterEnumeration.reachableResidues q
        [a 0, a 1, a 2, a 3, a 4, a 5] ↔
      ∃ x : FinitePipeline.Word6,
        OuterEnumeration.subsetSum a x.1 % q = target := by
  rw [mem_reachableResidues_iff_exists_choice]
  constructor
  · rintro ⟨choices, hlength, hchoose⟩
    have hlt : packBits choices < 64 := by
      have := packBits_lt_two_pow_length choices
      simpa [hlength] using this
    let x : FinitePipeline.Word6 := ⟨packBits choices, hlt⟩
    refine ⟨x, ?_⟩
    change OuterEnumeration.subsetSum a (packBits choices) % q = target
    rw [subsetSum_packBits_of_length_six a choices hlength]
    exact hchoose
  · rintro ⟨x, hx⟩
    refine ⟨[x.1.testBit 0, x.1.testBit 1, x.1.testBit 2,
      x.1.testBit 3, x.1.testBit 4, x.1.testBit 5], rfl, ?_⟩
    rw [choiceSum_wordBits]
    exact hx

/-- `HasSecondFiber` exposes exactly one of the 64 concrete words. -/
theorem hasSecondFiber_iff_exists_word (r : OuterEnumeration.RawRecord) :
    OuterEnumeration.HasSecondFiber r = true ↔
      ∃ x : FinitePipeline.Word6,
        OuterEnumeration.subsetSum r.a x.1 % r.q = r.q / r.m := by
  simpa [OuterEnumeration.HasSecondFiber] using
    mem_reachableResidues_six_iff_word r.q (r.q / r.m) r.a

/-- The direct `List.range 64` implementation has the same concrete-word
semantics. -/
theorem hasSecondFiberByMasks_iff_exists_word (r : OuterEnumeration.RawRecord) :
    OuterEnumeration.HasSecondFiberByMasks r = true ↔
      ∃ x : FinitePipeline.Word6,
        OuterEnumeration.subsetSum r.a x.1 % r.q = r.q / r.m := by
  simp only [OuterEnumeration.HasSecondFiberByMasks, List.any_eq_true]
  constructor
  · rintro ⟨mask, hmask, heq⟩
    have hlt : mask < 64 := List.mem_range.mp hmask
    refine ⟨⟨mask, hlt⟩, ?_⟩
    simpa using heq
  · rintro ⟨x, hx⟩
    refine ⟨x.1, List.mem_range.mpr x.2, ?_⟩
    simpa using hx

/-- The two independently implemented nonemptiness tests are extensionally
equal.  No positivity assumption is needed; in particular this also checks
that their behavior agrees on malformed zero-modulus records. -/
theorem hasSecondFiber_eq_hasSecondFiberByMasks
    (r : OuterEnumeration.RawRecord) :
    OuterEnumeration.HasSecondFiber r =
      OuterEnumeration.HasSecondFiberByMasks r := by
  apply Bool.eq_iff_iff.mpr
  exact hasSecondFiber_iff_exists_word r |>.trans
    (hasSecondFiberByMasks_iff_exists_word r).symm

/-- The second-fiber Boolean is true exactly when the actual finite residue
fiber is nonempty. -/
theorem hasSecondFiber_iff_residueFiber_nonempty
    (r : OuterEnumeration.RawRecord) :
    OuterEnumeration.HasSecondFiber r = true ↔
      (residueFiber r (r.q / r.m)).Nonempty := by
  rw [hasSecondFiber_iff_exists_word]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_residueFiber_iff r (r.q / r.m) x).2 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_residueFiber_iff r (r.q / r.m) x).1 hx⟩

/-- Direct provenance statement for the constructed pipeline pair: its second
mask is nonempty exactly when the enumerator's second-fiber test succeeds. -/
theorem hasSecondFiber_iff_recordFiberPair_mask1_nonempty
    (r : OuterEnumeration.RawRecord) :
    OuterEnumeration.HasSecondFiber r = true ↔
      ∃ x : FinitePipeline.Word6,
        FinitePipeline.InMask (recordFiberPair r).mask1 x := by
  rw [hasSecondFiber_iff_exists_word]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (in_recordFiberPair_mask1_iff r x).2 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (in_recordFiberPair_mask1_iff r x).1 hx⟩

/-! ## Connection to the genuine `SS.weight` residue fiber -/

/-- Interpret a pipeline word as the corresponding six-qubit Boolean string. -/
def wordBitString (x : FinitePipeline.Word6) : SS.BitString 6 :=
  fun i => x.1.testBit i.1

/-- The executable natural subset sum is the genuine `SS.weight` after
casting the angle entries into `ZMod q`. -/
theorem weight_wordBitString_eq_subsetSum (r : OuterEnumeration.RawRecord)
    (hq : 0 < r.q) (x : FinitePipeline.Word6) :
    letI : NeZero r.q := ⟨Nat.ne_of_gt hq⟩
    SS.weight (fun i => (r.a i : ZMod r.q)) (wordBitString x) =
      (OuterEnumeration.subsetSum r.a x.1 : ZMod r.q) := by
  letI : NeZero r.q := ⟨Nat.ne_of_gt hq⟩
  simp [SS.weight, SS.bit, wordBitString, OuterEnumeration.subsetSum,
    Fin.sum_univ_succ]
  ring

/-- The actual gate-theoretic residue fiber, represented on the same 64 words
as `FinitePipeline`. -/
def gateResidueFiber (r : OuterEnumeration.RawRecord) (hq : 0 < r.q)
    (residue : ℕ) : Finset FinitePipeline.Word6 :=
  letI : NeZero r.q := ⟨Nat.ne_of_gt hq⟩
  Finset.univ.filter fun x =>
    SS.weight (fun i => (r.a i : ZMod r.q)) (wordBitString x) =
      (residue : ZMod r.q)

/-- For a canonical natural representative, membership in the natural and
gate-theoretic residue fibers is identical. -/
theorem mem_gateResidueFiber_iff (r : OuterEnumeration.RawRecord)
    (hq : 0 < r.q) (residue : ℕ) (hresidue : residue < r.q)
    (x : FinitePipeline.Word6) :
    x ∈ gateResidueFiber r hq residue ↔
      OuterEnumeration.subsetSum r.a x.1 % r.q = residue := by
  letI : NeZero r.q := ⟨Nat.ne_of_gt hq⟩
  rw [gateResidueFiber]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [weight_wordBitString_eq_subsetSum r hq x]
  constructor
  · intro h
    have hval := congrArg ZMod.val h
    simpa [ZMod.val_natCast_of_lt (Nat.mod_lt _ hq),
      ZMod.val_natCast_of_lt hresidue] using hval
  · intro h
    rw [← h]
    exact (ZMod.natCast_mod (OuterEnumeration.subsetSum r.a x.1) r.q).symm

/-- Under the nondegenerate logical-order condition used by the outer
enumeration, `HasSecondFiber` is nonemptiness of the genuine `SS.weight`
fiber at residue `q / m`. -/
theorem hasSecondFiber_iff_gateResidueFiber_nonempty
    (r : OuterEnumeration.RawRecord) (hq : 0 < r.q) (hm : 1 < r.m) :
    OuterEnumeration.HasSecondFiber r = true ↔
      (gateResidueFiber r hq (r.q / r.m)).Nonempty := by
  have htarget : r.q / r.m < r.q :=
    Nat.div_lt_self hq hm
  rw [hasSecondFiber_iff_exists_word]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_gateResidueFiber_iff r hq _ htarget x).2 hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_gateResidueFiber_iff r hq _ htarget x).1 hx⟩

end MainTheory.OuterCompleteness
