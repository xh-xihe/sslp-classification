import MainTheory.FinitePipeline
import MainTheory.MomentPolytope
import MainTheory.CubeAction
import MainTheory.AffineRankCertificate

/-!
# Bridges between the three degree-two moment models

This file contains only semantic conversion theorems.  In particular, it does
not identify `Fin 64` with `Fin 6 → Bool` by definitional equality: the map from
a finite-pipeline word to its six Boolean coordinates is written explicitly.
-/

namespace MainTheory.MomentModelBridge

open scoped BigOperators

namespace PipelineToPolytope

open MainTheory.FinitePipeline
open MainTheory.MomentPolytope

set_option maxHeartbeats 800000

/-- The actual Boolean point encoded by a finite-pipeline word. -/
def wordPoint (x : Word6) : BitPoint6 := fun j => x.1.testBit j.1

/-- Cast the two exact rational weight blocks, without reindexing them. -/
def castWeight (p0 p1 : Word6 → ℚ) : Sum Word6 Word6 → ℝ
  | Sum.inl x => p0 x
  | Sum.inr x => p1 x

/-- The first six pipeline rows really are the six Boolean coordinates. -/
def singleIndex (j : Fin 6) : Fin 21 := ⟨j.1, Nat.lt_trans j.2 (by decide)⟩

/-- The pipeline's documented lexicographic order on the fifteen pairs. -/
def pairIndex (j k : Fin 6) : Fin 21 :=
  if j = 0 then
    if k = 1 then 6 else if k = 2 then 7 else if k = 3 then 8 else
      if k = 4 then 9 else if k = 5 then 10 else 0
  else if j = 1 then
    if k = 2 then 11 else if k = 3 then 12 else if k = 4 then 13 else
      if k = 5 then 14 else 0
  else if j = 2 then
    if k = 3 then 15 else if k = 4 then 16 else if k = 5 then 17 else 0
  else if j = 3 then
    if k = 4 then 18 else if k = 5 then 19 else 0
  else if j = 4 then
    if k = 5 then 20 else 0
  else 0

abbrev MomentRow := Sum (Fin 6) Pair6

def rowIndex : MomentRow → Fin 21
  | Sum.inl j => singleIndex j
  | Sum.inr jk => pairIndex jk.1.1 jk.1.2

/-- The documented six-plus-fifteen indexing covers every pipeline row. -/
theorem rowIndex_surjective (k : Fin 21) : ∃ r : MomentRow, rowIndex r = k := by
  fin_cases k <;>
    first
    | exact ⟨Sum.inl (0 : Fin 6), rfl⟩
    | exact ⟨Sum.inl (1 : Fin 6), rfl⟩
    | exact ⟨Sum.inl (2 : Fin 6), rfl⟩
    | exact ⟨Sum.inl (3 : Fin 6), rfl⟩
    | exact ⟨Sum.inl (4 : Fin 6), rfl⟩
    | exact ⟨Sum.inl (5 : Fin 6), rfl⟩
    | exact ⟨Sum.inr ⟨((0 : Fin 6), (1 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((0 : Fin 6), (2 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((0 : Fin 6), (3 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((0 : Fin 6), (4 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((0 : Fin 6), (5 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((1 : Fin 6), (2 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((1 : Fin 6), (3 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((1 : Fin 6), (4 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((1 : Fin 6), (5 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((2 : Fin 6), (3 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((2 : Fin 6), (4 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((2 : Fin 6), (5 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((3 : Fin 6), (4 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((3 : Fin 6), (5 : Fin 6)), by decide⟩, rfl⟩
    | exact ⟨Sum.inr ⟨((4 : Fin 6), (5 : Fin 6)), by decide⟩, rfl⟩

@[simp] theorem coord_wordPoint (x : Word6) (j : Fin 6) :
    coord (wordPoint x) j = (bit x j : ℝ) := by
  by_cases h : x.1.testBit j.1 <;> simp [wordPoint, coord, bit, h]

@[simp] theorem feature_single (x : Word6) (j : Fin 6) :
    feature x (singleIndex j) = bit x j := by
  fin_cases j <;> rfl

theorem feature_pair (x : Word6) (j k : Fin 6) (hjk : j < k) :
    feature x (pairIndex j k) = bit x j * bit x k := by
  fin_cases j <;> fin_cases k <;>
    simp_all [pairIndex, feature]

private theorem cast_sum_mul_feature_single (p : Word6 → ℚ) (j : Fin 6) :
    ((∑ x, p x * feature x (singleIndex j) : ℚ) : ℝ) =
      ∑ x, (p x : ℝ) * coord (wordPoint x) j := by
  rw [Rat.cast_sum]
  simp only [Rat.cast_mul, feature_single, coord_wordPoint]

private theorem cast_sum_mul_feature_pair (p : Word6 → ℚ)
    (j k : Fin 6) (hjk : j < k) :
    ((∑ x, p x * feature x (pairIndex j k) : ℚ) : ℝ) =
      ∑ x, (p x : ℝ) * coord (wordPoint x) j * coord (wordPoint x) k := by
  rw [Rat.cast_sum]
  simp only [Rat.cast_mul, feature_pair _ _ _ hjk, coord_wordPoint, mul_assoc]

/-- A kernel-checked rational pipeline witness is a witness for the concrete
paper-facing real moment polytope after the explicit scalar cast. -/
theorem feasible_cast {pair : FiberPair} {p0 p1 : Word6 → ℚ}
    (h : MainTheory.FinitePipeline.Feasible pair p0 p1) :
    MainTheory.MomentPolytope.Feasible wordPoint wordPoint (castWeight p0 p1) := by
  refine {
    nonneg := ?_
    norm0 := ?_
    norm1 := ?_
    firstMoment := ?_
    secondMoment := ?_ }
  · rintro (x | x)
    · have hx : (0 : ℝ) ≤ (p0 x : ℝ) := by exact_mod_cast h.nonneg0 x
      simpa [castWeight] using hx
    · have hx : (0 : ℝ) ≤ (p1 x : ℝ) := by exact_mod_cast h.nonneg1 x
      simpa [castWeight] using hx
  · have hn : (∑ x, (p0 x : ℝ)) = 1 := by exact_mod_cast h.norm0
    simpa [castWeight] using hn
  · have hn : (∑ x, (p1 x : ℝ)) = 1 := by exact_mod_cast h.norm1
    simpa [castWeight] using hn
  · intro j
    have hm := congrArg (fun q : ℚ => (q : ℝ)) (h.moments (singleIndex j))
    change ((∑ x, p0 x * feature x (singleIndex j) : ℚ) : ℝ) =
      ((∑ x, p1 x * feature x (singleIndex j) : ℚ) : ℝ) at hm
    rw [cast_sum_mul_feature_single, cast_sum_mul_feature_single] at hm
    simpa [mean0, mean1, castWeight] using hm
  · rintro ⟨⟨j, k⟩, hjk⟩
    have hm := congrArg (fun q : ℚ => (q : ℝ)) (h.moments (pairIndex j k))
    change ((∑ x, p0 x * feature x (pairIndex j k) : ℚ) : ℝ) =
      ((∑ x, p1 x * feature x (pairIndex j k) : ℚ) : ℝ) at hm
    rw [cast_sum_mul_feature_pair _ _ _ hjk,
      cast_sum_mul_feature_pair _ _ _ hjk] at hm
    simpa [second0, second1, castWeight] using hm

/-- Exact rational lifts of a real weight vector.  This is the precise extra
condition needed for the elementary reverse bridge; arbitrary real feasible
points are not silently asserted to have rational coordinates. -/
def IsRationalLift (p0 p1 : Word6 → ℚ) (p : Sum Word6 Word6 → ℝ) : Prop :=
  (∀ x, p (Sum.inl x) = (p0 x : ℝ)) ∧
  (∀ x, p (Sum.inr x) = (p1 x : ℝ))

private theorem rational_single_row_of_lift
    {p0 p1 : Word6 → ℚ} {p : Sum Word6 Word6 → ℝ}
    (hp : IsRationalLift p0 p1 p)
    (h : MainTheory.MomentPolytope.Feasible wordPoint wordPoint p)
    (j : Fin 6) :
    ∑ x, p0 x * feature x (singleIndex j) =
      ∑ x, p1 x * feature x (singleIndex j) := by
  apply Rat.cast_injective (α := ℝ)
  change ((∑ x, p0 x * feature x (singleIndex j) : ℚ) : ℝ) =
    ((∑ x, p1 x * feature x (singleIndex j) : ℚ) : ℝ)
  rw [cast_sum_mul_feature_single, cast_sum_mul_feature_single]
  simpa [mean0, mean1, hp.1, hp.2] using h.firstMoment j

private theorem rational_pair_row_of_lift
    {p0 p1 : Word6 → ℚ} {p : Sum Word6 Word6 → ℝ}
    (hp : IsRationalLift p0 p1 p)
    (h : MainTheory.MomentPolytope.Feasible wordPoint wordPoint p)
    (j k : Fin 6) (hjk : j < k) :
    ∑ x, p0 x * feature x (pairIndex j k) =
      ∑ x, p1 x * feature x (pairIndex j k) := by
  apply Rat.cast_injective (α := ℝ)
  change ((∑ x, p0 x * feature x (pairIndex j k) : ℚ) : ℝ) =
    ((∑ x, p1 x * feature x (pairIndex j k) : ℚ) : ℝ)
  rw [cast_sum_mul_feature_pair _ _ _ hjk,
    cast_sum_mul_feature_pair _ _ _ hjk]
  simpa [second0, second1, hp.1, hp.2] using
    h.secondMoment ⟨⟨j, k⟩, hjk⟩

/-- Conditional converse.  A paper-facing real witness whose two blocks are
pointwise casts of rational blocks, and whose rational blocks obey the masks,
is an exact finite-pipeline witness.  The extra hypotheses express precisely
the rationality and support information absent from `MomentPolytope.Feasible`;
none is a moment equation or a restatement of the conclusion. -/
theorem feasible_of_rational_lift {pair : FiberPair} {p0 p1 : Word6 → ℚ}
    {p : Sum Word6 Word6 → ℝ}
    (hp : IsRationalLift p0 p1 p)
    (hs0 : ∀ x, ¬ InMask pair.mask0 x → p0 x = 0)
    (hs1 : ∀ x, ¬ InMask pair.mask1 x → p1 x = 0)
    (h : MainTheory.MomentPolytope.Feasible wordPoint wordPoint p) :
    MainTheory.FinitePipeline.Feasible pair p0 p1 where
  support0 := hs0
  support1 := hs1
  nonneg0 x := by
    have hx := h.nonneg (Sum.inl x)
    rw [hp.1 x] at hx
    exact_mod_cast hx
  nonneg1 x := by
    have hx := h.nonneg (Sum.inr x)
    rw [hp.2 x] at hx
    exact_mod_cast hx
  norm0 := by
    have hn := h.norm0
    simp only [hp.1] at hn
    exact_mod_cast hn
  norm1 := by
    have hn := h.norm1
    simp only [hp.2] at hn
    exact_mod_cast hn
  moments := by
    intro k
    obtain ⟨r, hr⟩ := rowIndex_surjective k
    rw [← hr]
    rcases r with j | ⟨⟨j, k⟩, hjk⟩
    · exact rational_single_row_of_lift hp h j
    · exact rational_pair_row_of_lift hp h j k hjk


end PipelineToPolytope

namespace WalshMonomial

open MainTheory.MomentPolytope
open MainTheory.CubeAction

abbrev Cube6 := SS.BitString 6

def mass (p : Bool → Cube6 → ℝ) (c : Bool) : ℝ := ∑ x, p c x

def first (p : Bool → Cube6 → ℝ) (c : Bool) (j : Fin 6) : ℝ :=
  ∑ x, p c x * coord x j

def second (p : Bool → Cube6 → ℝ) (c : Bool) (j k : Fin 6) : ℝ :=
  ∑ x, p c x * coord x j * coord x k

def walsh (p : Bool → Cube6 → ℝ) (c : Bool) (z : Cube6) : ℝ :=
  ∑ x, p c x * character z x

def singleMask (j : Fin 6) : Cube6 := fun i => i == j

def pairMask (j k : Fin 6) : Cube6 := SS.bxor (singleMask j) (singleMask k)

def zeroMask : Cube6 := fun _ => false

def trueSupport (z : Cube6) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => z i = true)

@[simp] theorem mem_trueSupport (z : Cube6) (i : Fin 6) :
    i ∈ trueSupport z ↔ z i = true := by
  simp [trueSupport]

theorem hammingWt_eq_card_trueSupport (z : Cube6) :
    SS.hammingWt z = (trueSupport z).card := rfl

private theorem eq_zeroMask_of_support_empty {z : Cube6}
    (h : trueSupport z = ∅) : z = zeroMask := by
  funext i
  have hi : i ∉ trueSupport z := by simp [h]
  cases hiz : z i
  · rfl
  · exact (hi (by simp [hiz])).elim

private theorem eq_singleMask_of_support_singleton {z : Cube6} {j : Fin 6}
    (h : trueSupport z = {j}) : z = singleMask j := by
  funext i
  by_cases hij : i = j
  · subst i
    have hj : j ∈ trueSupport z := by simp [h]
    simp [singleMask, (mem_trueSupport z j).1 hj]
  · have hi : i ∉ trueSupport z := by simp [h, hij]
    cases hiz : z i
    · simp [singleMask, hij]
    · exact (hi (by simp [hiz])).elim

private theorem eq_pairMask_of_support_pair {z : Cube6} {j k : Fin 6}
    (hjk : j ≠ k) (h : trueSupport z = {j, k}) : z = pairMask j k := by
  funext i
  by_cases hij : i = j
  · subst i
    have hj : j ∈ trueSupport z := by simp [h]
    simp [pairMask, singleMask, SS.bxor, hjk,
      (mem_trueSupport z j).1 hj]
  · by_cases hik : i = k
    · subst i
      have hk : k ∈ trueSupport z := by simp [h]
      simp [pairMask, singleMask, SS.bxor, hij,
        (mem_trueSupport z k).1 hk]
    · have hi : i ∉ trueSupport z := by simp [h, hij, hik]
      cases hiz : z i
      · simp [pairMask, singleMask, SS.bxor, hij, hik]
      · exact (hi (by simp [hiz])).elim

/-- Every six-bit mask of Hamming weight at most two is exactly the zero mask,
a singleton mask, or one uniquely orderable two-coordinate mask. -/
theorem lowWeight_mask_classification (z : Cube6) (hz : SS.hammingWt z ≤ 2) :
    z = zeroMask ∨ (∃ j, z = singleMask j) ∨
      ∃ jk : Pair6, z = pairMask jk.1.1 jk.1.2 := by
  have hc : (trueSupport z).card = 0 ∨ (trueSupport z).card = 1 ∨
      (trueSupport z).card = 2 := by
    rw [hammingWt_eq_card_trueSupport] at hz
    omega
  rcases hc with hc | hc | hc
  · exact Or.inl (eq_zeroMask_of_support_empty (Finset.card_eq_zero.mp hc))
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
    exact Or.inr (Or.inl ⟨j, eq_singleMask_of_support_singleton hj⟩)
  · obtain ⟨j, k, hjk, hs⟩ := Finset.card_eq_two.mp hc
    rcases lt_or_gt_of_ne hjk with hjk' | hkj'
    · exact Or.inr (Or.inr ⟨⟨⟨j, k⟩, hjk'⟩,
        eq_pairMask_of_support_pair hjk hs⟩)
    · have hs' : trueSupport z = {k, j} := by simpa [Finset.pair_comm] using hs
      exact Or.inr (Or.inr ⟨⟨⟨k, j⟩, hkj'⟩,
        eq_pairMask_of_support_pair hjk.symm hs'⟩)

private theorem bdot_comm (s t : Cube6) : SS.bdot s t = SS.bdot t s := by
  unfold SS.bdot
  congr 3
  ext i
  simp [Bool.and_comm]

theorem character_single (x : Cube6) (j : Fin 6) :
    character (singleMask j) x = 1 - 2 * coord x j := by
  have hb : SS.bdot (singleMask j) x = x j := by
    unfold SS.bdot
    have hf :
        (Finset.univ.filter (fun i : Fin 6 => singleMask j i && x i)) =
          if x j then {j} else ∅ := by
      ext i
      by_cases hij : i = j
      · subst i
        cases h : x j <;> simp [singleMask, h]
      · cases h : x j <;> simp [singleMask, hij]
    rw [hf]
    cases h : x j <;> simp
  rw [character, hb]
  cases h : x j <;> norm_num [boolSign, coord, h]

private theorem character_pair_product (x : Cube6) (j k : Fin 6) :
    character (pairMask j k) x = character (singleMask j) x * character (singleMask k) x := by
  unfold character pairMask
  rw [bdot_comm, SixQubit.CodeEquiv.bdot_bxor_right,
    ← bdot_comm x (singleMask j),
    ← bdot_comm x (singleMask k), boolSign_xor]

theorem character_pair (x : Cube6) (j k : Fin 6) (_hjk : j ≠ k) :
    character (pairMask j k) x =
      1 - 2 * coord x j - 2 * coord x k + 4 * (coord x j * coord x k) := by
  rw [character_pair_product, character_single, character_single]
  ring

theorem hammingWt_singleMask (j : Fin 6) : SS.hammingWt (singleMask j) = 1 := by
  fin_cases j <;> decide

theorem hammingWt_pairMask (j k : Fin 6) (hjk : j ≠ k) :
    SS.hammingWt (pairMask j k) = 2 := by
  fin_cases j <;> fin_cases k <;>
    simp_all [SS.hammingWt, pairMask, singleMask, SS.bxor] <;> decide

theorem walsh_single_formula (p : Bool → Cube6 → ℝ) (c : Bool) (j : Fin 6) :
    walsh p c (singleMask j) = mass p c - 2 * first p c j := by
  simp_rw [walsh, character_single]
  unfold mass first
  calc
    (∑ x, p c x * (1 - 2 * coord x j)) =
        ∑ x, (p c x - 2 * (p c x * coord x j)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem walsh_pair_formula (p : Bool → Cube6 → ℝ) (c : Bool)
    (j k : Fin 6) (hjk : j ≠ k) :
    walsh p c (pairMask j k) =
      mass p c - 2 * first p c j - 2 * first p c k + 4 * second p c j k := by
  simp_rw [walsh, character_pair _ _ _ hjk]
  unfold mass first second
  calc
    (∑ x, p c x *
        (1 - 2 * coord x j - 2 * coord x k + 4 * (coord x j * coord x k))) =
      ∑ x, (p c x - 2 * (p c x * coord x j) -
        2 * (p c x * coord x k) + 4 * (p c x * coord x j * coord x k)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Equality of the constant, six linear, and fifteen square-free monomial
moments between the two colours. -/
structure MonomialEqual (p : Bool → Cube6 → ℝ) : Prop where
  mass : mass p false = mass p true
  first : ∀ j, first p false j = first p true j
  second : ∀ jk : Pair6, second p false jk.1.1 jk.1.2 = second p true jk.1.1 jk.1.2

/-- The same 22 coordinates in the explicit Walsh basis. -/
structure WalshBasisEqual (p : Bool → Cube6 → ℝ) : Prop where
  mass : mass p false = mass p true
  single : ∀ j, walsh p false (singleMask j) = walsh p true (singleMask j)
  pair : ∀ jk : Pair6,
    walsh p false (pairMask jk.1.1 jk.1.2) =
      walsh p true (pairMask jk.1.1 jk.1.2)

theorem character_zero (x : Cube6) : character zeroMask x = 1 := by
  simp [character, zeroMask, SS.bdot, boolSign]

theorem walsh_zero_formula (p : Bool → Cube6 → ℝ) (c : Bool) :
    walsh p c zeroMask = mass p c := by
  simp [walsh, mass, character_zero]

/-- CubeAction's full quantified low-weight Walsh condition, including its
constant row as a named field. -/
structure DegreeTwoWalshEqual (p : Bool → Cube6 → ℝ) : Prop where
  mass : mass p false = mass p true
  moments : ∀ z, SS.hammingWt z ≤ 2 → walsh p false z = walsh p true z

/-- The 22 explicit Walsh rows are neither an undercount nor an approximation:
they are equivalent to quantifying over every mask of Hamming weight at most
two. -/
theorem degreeTwoWalshEqual_iff_walshBasisEqual (p : Bool → Cube6 → ℝ) :
    DegreeTwoWalshEqual p ↔ WalshBasisEqual p := by
  constructor
  · intro h
    refine ⟨h.mass, ?_, ?_⟩
    · intro j
      exact h.moments _ (by simp [hammingWt_singleMask])
    · rintro ⟨⟨j, k⟩, hjk⟩
      exact h.moments _ (by simp [hammingWt_pairMask _ _ (ne_of_lt hjk)])
  · intro h
    refine ⟨h.mass, ?_⟩
    intro z hz
    rcases lowWeight_mask_classification z hz with hz0 | ⟨j, hj⟩ | ⟨jk, hjk⟩
    · subst z
      simpa [walsh_zero_formula] using h.mass
    · subst z
      exact h.single j
    · subst z
      exact h.pair jk

/-- The explicit triangular change of coordinates is invertible: normalized
degree-at-most-two monomial equality is equivalent to Walsh-basis equality. -/
theorem walshBasisEqual_iff_monomialEqual (p : Bool → Cube6 → ℝ) :
    WalshBasisEqual p ↔ MonomialEqual p := by
  constructor
  · intro h
    have hf : ∀ j, first p false j = first p true j := by
      intro j
      have hw := h.single j
      rw [walsh_single_formula, walsh_single_formula] at hw
      linarith [h.mass]
    refine ⟨h.mass, hf, ?_⟩
    rintro ⟨⟨j, k⟩, hjk⟩
    have hw := h.pair ⟨⟨j, k⟩, hjk⟩
    rw [walsh_pair_formula _ _ _ _ (ne_of_lt hjk),
      walsh_pair_formula _ _ _ _ (ne_of_lt hjk)] at hw
    linarith [h.mass, hf j, hf k]
  · intro h
    refine ⟨h.mass, ?_, ?_⟩
    · intro j
      rw [walsh_single_formula, walsh_single_formula, h.mass, h.first j]
    · rintro ⟨⟨j, k⟩, hjk⟩
      rw [walsh_pair_formula _ _ _ _ (ne_of_lt hjk),
        walsh_pair_formula _ _ _ _ (ne_of_lt hjk), h.mass,
        h.first j, h.first k, h.second ⟨⟨j, k⟩, hjk⟩]

/-- Full `hammingWt ≤ 2` Walsh equality is exactly the paper's degree-two
monomial equality. -/
theorem degreeTwoWalshEqual_iff_monomialEqual (p : Bool → Cube6 → ℝ) :
    DegreeTwoWalshEqual p ↔ MonomialEqual p :=
  (degreeTwoWalshEqual_iff_walshBasisEqual p).trans
    (walshBasisEqual_iff_monomialEqual p)

/-- Every CubeAction witness supplies exactly the monomial moments used by the
paper-facing model. -/
theorem monomialEqual_of_momentWitness {F : MainTheory.CubeAction.FiberPair 6}
    (W : MomentWitness F) : MonomialEqual W.weight := by
  apply (walshBasisEqual_iff_monomialEqual W.weight).1
  refine ⟨(W.normalized false).trans (W.normalized true).symm, ?_, ?_⟩
  · intro j
    exact W.moments _ (by simp [hammingWt_singleMask])
  · rintro ⟨⟨j, k⟩, hjk⟩
    exact W.moments _ (by simp [hammingWt_pairMask _ _ (ne_of_lt hjk)])

/-- Conversely, monomial equality plus the three non-moment witness conditions
constructs CubeAction's complete quantified witness. -/
def momentWitnessOfMonomial {F : MainTheory.CubeAction.FiberPair 6}
    (p : Bool → Cube6 → ℝ)
    (hnonneg : ∀ c x, 0 ≤ p c x)
    (hsupported : ∀ c x, p c x ≠ 0 → x ∈ F c)
    (hnormalized : ∀ c, ∑ x, p c x = 1)
    (hm : MonomialEqual p) : MomentWitness F where
  weight := p
  nonneg := hnonneg
  supported := hsupported
  normalized := hnormalized
  moments := ((degreeTwoWalshEqual_iff_monomialEqual p).2 hm).moments

end WalshMonomial

namespace RankCast

open MainTheory.FinitePipeline
open MainTheory.AffineRankCertificate

abbrev RealVec6 := Fin 6 → ℝ

/-- Coordinatewise scalar extension of the exact Boolean point. -/
def realPoint (x : Word6) : RealVec6 := fun j => (point x j : ℝ)

def realMaskPointSet (mask : ℕ) : Set RealVec6 :=
  realPoint '' {x : Word6 | InMask mask x}

/-- The `ActiveFace` notion of affine rank applied to precisely the same mask. -/
noncomputable def realMaskAffineRank (mask : ℕ) : ℕ :=
  MainTheory.ActiveFace.affineRank (realMaskPointSet mask)

theorem realPoint_eq_bitVec_wordPoint (x : Word6) :
    realPoint x = MainTheory.CubeAction.bitVec
      (PipelineToPolytope.wordPoint x) := by
  funext j
  by_cases h : x.1.testBit j.1 <;>
    simp [realPoint, point, bit, MainTheory.CubeAction.bitVec,
      PipelineToPolytope.wordPoint, h]

def realBasePoint (d : Data) : RealVec6 := realPoint d.baseWord

def realLowerDiff (d : Data) (i : Fin d.rank) : RealVec6 :=
  realPoint (d.lowerWord i) - realBasePoint d

def realLowerRestriction (d : Data) : RealVec6 →ₗ[ℝ] (Fin d.rank → ℝ) where
  toFun v j := v (d.lowerCoord j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def realLowerMinor (d : Data) : Matrix (Fin d.rank) (Fin d.rank) ℝ :=
  fun i j => realLowerDiff d i (d.lowerCoord j)

private theorem realLowerMinor_eq_map (d : Data) :
    realLowerMinor d = d.lowerMinor.map (Rat.castHom ℝ) := by
  ext i j
  simp [realLowerMinor, realLowerDiff, realBasePoint, realPoint,
    Data.lowerMinor, Data.lowerDiff, Data.basePoint]

private theorem realLowerMinor_det_ne {mask : ℕ} {d : Data}
    (h : LowerValid mask d) : (realLowerMinor d).det ≠ 0 := by
  intro hz
  rw [realLowerMinor_eq_map] at hz
  change (d.lowerMinor.map (fun x : ℚ => (x : ℝ))).det = 0 at hz
  rw [← Rat.cast_det] at hz
  apply h.minor_ne
  apply Rat.cast_injective (α := ℝ)
  simpa using hz

private theorem realBasePoint_mem {mask : ℕ} {d : Data}
    (h : LowerValid mask d) : realBasePoint d ∈ realMaskPointSet mask :=
  ⟨d.baseWord, h.base_mem, rfl⟩

private theorem realLowerPoint_mem {mask : ℕ} {d : Data}
    (h : LowerValid mask d) (i : Fin d.rank) :
    realPoint (d.lowerWord i) ∈ realMaskPointSet mask :=
  ⟨d.lowerWord i, h.lower_mem i, rfl⟩

private theorem realLowerDiff_mem_direction {mask : ℕ} {d : Data}
    (h : LowerValid mask d) (i : Fin d.rank) :
    realLowerDiff d i ∈ (affineSpan ℝ (realMaskPointSet mask)).direction := by
  exact AffineSubspace.vsub_mem_direction
    (mem_affineSpan ℝ (realLowerPoint_mem h i))
    (mem_affineSpan ℝ (realBasePoint_mem h))

private theorem realLowerDiff_linearIndependent {mask : ℕ} {d : Data}
    (h : LowerValid mask d) : LinearIndependent ℝ (realLowerDiff d) := by
  apply LinearIndependent.of_comp (realLowerRestriction d)
  change LinearIndependent ℝ (realLowerMinor d)
  exact Matrix.linearIndependent_rows_of_det_ne_zero (realLowerMinor_det_ne h)

private theorem rank_le_realMaskAffineRank {mask : ℕ} {d : Data}
    (h : LowerValid mask d) : d.rank ≤ realMaskAffineRank mask := by
  let D := (affineSpan ℝ (realMaskPointSet mask)).direction
  let v : Fin d.rank → D := fun i => ⟨realLowerDiff d i, realLowerDiff_mem_direction h i⟩
  have hv : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp D.subtype
    simpa [v] using realLowerDiff_linearIndependent h
  simpa [realMaskAffineRank, MainTheory.ActiveFace.affineRank, D] using
    hv.fintype_card_le_finrank

def realNormalVec (d : Data) (i : Fin (6 - d.rank)) : RealVec6 :=
  fun j => (d.normalVec i j : ℝ)

def realDot (u v : RealVec6) : ℝ := ∑ j, u j * v j

def realNormalFunctional (d : Data) (i : Fin (6 - d.rank)) :
    Module.Dual ℝ RealVec6 where
  toFun v := realDot (realNormalVec d i) v
  map_add' x y := by
    simp only [realDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [realDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [RingHom.id_apply]
    ring

def realStdBasisVec (j : Fin 6) : RealVec6 := fun k => if k = j then 1 else 0

def realNormalRestriction (d : Data) :
    Module.Dual ℝ RealVec6 →ₗ[ℝ] (Fin (6 - d.rank) → ℝ) where
  toFun f j := f (realStdBasisVec (d.normalCoord j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def realNormalMinor (d : Data) :
    Matrix (Fin (6 - d.rank)) (Fin (6 - d.rank)) ℝ :=
  fun i j => realNormalFunctional d i (realStdBasisVec (d.normalCoord j))

private theorem realNormal_eval_diff (d : Data) (i : Fin (6 - d.rank))
    (x : Word6) :
    realNormalFunctional d i (realPoint x - realBasePoint d) =
      (d.normalFunctional i (point x - d.basePoint) : ℝ) := by
  change (∑ j, (d.normalVec i j : ℝ) *
      ((point x j : ℝ) - (d.basePoint j : ℝ))) =
    ((∑ j, d.normalVec i j * (point x j - d.basePoint j) : ℚ) : ℝ)
  rw [Rat.cast_sum]
  simp

private theorem realNormalMinor_eq_map (d : Data) :
    realNormalMinor d = d.normalMinor.map (Rat.castHom ℝ) := by
  ext i j
  simp [realNormalMinor, realNormalFunctional, realDot, realNormalVec,
    realStdBasisVec, Data.normalMinor, Data.normalFunctional, dot, stdBasisVec]

private theorem realNormalMinor_det_ne {mask : ℕ} {d : Data}
    (h : UpperValid mask d) : (realNormalMinor d).det ≠ 0 := by
  intro hz
  rw [realNormalMinor_eq_map] at hz
  change (d.normalMinor.map (fun x : ℚ => (x : ℝ))).det = 0 at hz
  rw [← Rat.cast_det] at hz
  apply h.minor_ne
  apply Rat.cast_injective (α := ℝ)
  simpa using hz

private theorem realMaskPointSet_subset_hyperplane {mask : ℕ} {d : Data}
    (h : UpperValid mask d) (i : Fin (6 - d.rank)) :
    realMaskPointSet mask ⊆
      AffineSubspace.mk' (realBasePoint d) (LinearMap.ker (realNormalFunctional d i)) := by
  rintro _ ⟨x, hx, rfl⟩
  change realPoint x - realBasePoint d ∈ LinearMap.ker (realNormalFunctional d i)
  rw [LinearMap.mem_ker, realNormal_eval_diff]
  exact_mod_cast h.annihilates x hx i

private theorem realDirection_le_normalKer {mask : ℕ} {d : Data}
    (h : UpperValid mask d) (i : Fin (6 - d.rank)) :
    (affineSpan ℝ (realMaskPointSet mask)).direction ≤
      LinearMap.ker (realNormalFunctional d i) := by
  have hd := AffineSubspace.direction_le
    (affineSpan_le.2 (realMaskPointSet_subset_hyperplane h i))
  simpa only [AffineSubspace.direction_mk'] using hd

private theorem realNormalFunctional_linearIndependent {mask : ℕ} {d : Data}
    (h : UpperValid mask d) : LinearIndependent ℝ (realNormalFunctional d) := by
  apply LinearIndependent.of_comp (realNormalRestriction d)
  change LinearIndependent ℝ (realNormalMinor d)
  exact Matrix.linearIndependent_rows_of_det_ne_zero (realNormalMinor_det_ne h)

private theorem realDirection_le_normalCoannihilator {mask : ℕ} {d : Data}
    (h : UpperValid mask d) :
    (affineSpan ℝ (realMaskPointSet mask)).direction ≤
      (Submodule.span ℝ (Set.range (realNormalFunctional d))).dualCoannihilator := by
  intro v hv
  rw [Submodule.mem_dualCoannihilator]
  intro f hf
  refine Submodule.span_induction (p := fun f _ => f v = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨i, rfl⟩
    exact realDirection_le_normalKer h i hv
  · rfl
  · intro f g _ _ hf hg
    simpa using congrArg₂ (· + ·) hf hg
  · intro a f _ hf
    simp [hf]

private theorem realNormalSpan_finrank {mask : ℕ} {d : Data}
    (h : UpperValid mask d) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (realNormalFunctional d))) =
      6 - d.rank := by
  rw [finrank_span_eq_card (realNormalFunctional_linearIndependent h)]
  simp

private theorem realNormalCoannihilator_finrank {mask : ℕ} {d : Data}
    (h : UpperValid mask d) :
    Module.finrank ℝ
        (Submodule.span ℝ (Set.range (realNormalFunctional d))).dualCoannihilator =
      d.rank := by
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (Submodule.span ℝ (Set.range (realNormalFunctional d)))
  rw [realNormalSpan_finrank h] at hdim
  have hvec : Module.finrank ℝ RealVec6 = 6 := by simp [RealVec6]
  rw [hvec] at hdim
  have hr := h.rank_le
  omega

private theorem realMaskAffineRank_le_rank {mask : ℕ} {d : Data}
    (h : UpperValid mask d) : realMaskAffineRank mask ≤ d.rank := by
  calc
    realMaskAffineRank mask ≤
        Module.finrank ℝ
          (Submodule.span ℝ (Set.range (realNormalFunctional d))).dualCoannihilator := by
      exact Submodule.finrank_mono (realDirection_le_normalCoannihilator h)
    _ = d.rank := realNormalCoannihilator_finrank h

private theorem realMaskPointSet_eq_empty {mask : ℕ} (h : MaskEmpty mask) :
    realMaskPointSet mask = ∅ := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (h x hx).elim
  · simp

private theorem realMaskAffineRank_eq_zero_of_empty {mask : ℕ} (h : MaskEmpty mask) :
    realMaskAffineRank mask = 0 := by
  rw [realMaskAffineRank, MainTheory.ActiveFace.affineRank,
    realMaskPointSet_eq_empty h]
  simp

private theorem realAffineRank_eq_of_valid {mask : ℕ} {d : Data}
    (h : d.Valid mask) : realMaskAffineRank mask = d.rank := by
  rcases h with h | h
  · rw [h.2]
    exact realMaskAffineRank_eq_zero_of_empty h.1
  · exact Nat.le_antisymm (realMaskAffineRank_le_rank h.2)
      (rank_le_realMaskAffineRank h.1)

/-- For every accepted exact certificate, scalar extension from `ℚ` to `ℝ`
does not change the affine rank of the selected zero-one mask points. -/
theorem affineRank_real_eq_rational_of_valid {mask : ℕ} {d : Data}
    (h : d.Valid mask) :
    MainTheory.ActiveFace.affineRank (realMaskPointSet mask) = maskAffineRank mask := by
  change realMaskAffineRank mask = maskAffineRank mask
  rw [realAffineRank_eq_of_valid h, affineRank_eq_of_valid h]

end RankCast

end MainTheory.MomentModelBridge
