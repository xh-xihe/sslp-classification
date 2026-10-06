import MainTheory.CodeFiberBridge
import MainTheory.RealMomentSeparatorBridge

/-!
# A code supplies a real moment point

`CoarseFilterUnconditional.keepAt_of_s0_of_feasible` keeps a row for a code
provided the code supplies two things: the `S_0` clause, which
`SortedPivotConstruction.exists_normalForm_s0Clause` now proves outright, and a
*real* feasible point of the row's two-colour moment programme.  The second
input had no supplier: `RealMomentSeparatorBridge.RealFeasible` was only ever
consumed, by the separator side.

This file supplies it.  The point is the code's own pair of probability
distributions, `|c(x)|^2` on the left fibre and `|d(y)|^2` on the right, and
the five obligations of `MomentPolytope.Feasible` are, in order: positivity of
a squared modulus, the two normalizations, and the paper's `eq:LP-first` and
`eq:LP-second` -- which `SixQubit.occOn_eq_of_hasDistance` and
`occ2On_eq_of_hasDistance` already derive from distance three alone.

The only real work is the index translation.  The moment programme is indexed
by pipeline words in a mask, the quantum side by Boolean strings; they are the
same data (`wordPoint` and `wordBitString` are the same function, and
`BitPoint6` and `SS.BitString 6` are the same type), so the translation is a
reindexing of finite sums along the bijection `wordBitString`.
-/

namespace MainTheory.CodeMomentPoint

open MainTheory
open MainTheory.FinitePipeline
open MainTheory.MomentPolytope
open MainTheory.RealMomentSeparatorBridge
open MainTheory.OuterCompleteness
open MainTheory.MomentModelBridge.PipelineToPolytope
open scoped BigOperators

/-! ## The two index sets are the same data -/

/-- A pipeline word and the Boolean string it names carry the same
coordinates.  Both sides are `fun j => x.1.testBit j.1`. -/
@[simp] theorem wordPoint_eq_wordBitString (x : Word6) :
    wordPoint x = wordBitString x := rfl

set_option maxRecDepth 8000 in
/-- `wordBitString` is injective: six bits determine a word below `64`. -/
theorem wordBitString_inj :
    ∀ x y : Word6, wordBitString x = wordBitString y → x = y := by decide

/-- The Boolean strings named by the words of a mask. -/
def fiberSet (mask : ℕ) : Finset (SS.BitString 6) :=
  (Finset.univ.filter (fun x : Word6 => InMask mask x)).image wordBitString

theorem mem_fiberSet_of_inMask {mask : ℕ} {x : Word6} (h : InMask mask x) :
    wordBitString x ∈ fiberSet mask :=
  Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- Reindexing a sum over the mask's Boolean strings as a sum over the
subtype of words the moment programme actually uses. -/
theorem sum_fiberSet (mask : ℕ) (f : SS.BitString 6 → ℝ) :
    ∑ s ∈ fiberSet mask, f s
      = ∑ x : {x : Word6 // InMask mask x}, f (wordBitString x.1) := by
  rw [fiberSet, Finset.sum_image (fun a _ b _ h => wordBitString_inj a b h)]
  exact Finset.sum_subtype _ (fun x => by simp) _

/-- A state supported inside a mask vanishes off that mask's Boolean
strings. -/
theorem eq_zero_of_not_mem_fiberSet {mask : ℕ} {c : SS.State 6 ℂ}
    (hsupp : ∀ x : Word6, c (wordBitString x) ≠ 0 → InMask mask x)
    (s : SS.BitString 6) (hs : s ∉ fiberSet mask) : c s = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := CodeFiberBridge.exists_word_bitString s
  rw [← hx] at hne hs
  exact hs (mem_fiberSet_of_inMask (hsupp x hne))

/-! ## The moment rows are the occupation numbers -/

/-- A `coord`-weighted sum over a fibre is the occupation number of that
coordinate.  This is `eq:LP-first`'s left-hand side, twice over. -/
theorem sum_coord_eq_occOn (mask : ℕ) (c : SS.State 6 ℂ) (j : Fin 6) :
    ∑ x : {x : Word6 // InMask mask x},
        Complex.normSq (c (wordBitString x.1)) * coord (wordPoint x.1) j
      = SixQubit.occOn (fiberSet mask) c j := by
  simp only [wordPoint_eq_wordBitString]
  have h := sum_fiberSet mask (fun s => Complex.normSq (c s) * coord s j)
  rw [← h, SixQubit.occOn, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases hs : s j = true <;> simp [coord, hs]

/-- The pair version, for `eq:LP-second`. -/
theorem sum_coord2_eq_occ2On (mask : ℕ) (c : SS.State 6 ℂ) (j k : Fin 6) :
    ∑ x : {x : Word6 // InMask mask x},
        Complex.normSq (c (wordBitString x.1)) * coord (wordPoint x.1) j
          * coord (wordPoint x.1) k
      = SixQubit.occ2On (fiberSet mask) c j k := by
  simp only [wordPoint_eq_wordBitString]
  have h := sum_fiberSet mask
    (fun s => Complex.normSq (c s) * coord s j * coord s k)
  rw [← h, SixQubit.occ2On, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases hj : s j = true <;> by_cases hk : s k = true <;>
    simp [coord, hj, hk]

/-! ## The point -/

/-- The code's own pair of probability distributions, as a weight on the
row's two fibres. -/
def weightOf (pair : FiberPair) (c d : SS.State 6 ℂ) : RealWeight pair
  | Sum.inl x => Complex.normSq (c (wordBitString x.1))
  | Sum.inr y => Complex.normSq (d (wordBitString y.1))

/-- **A code supplies a real feasible point of its row's moment programme.**

The hypotheses are exactly what a code in sorted normal form gives: its two
logical words are supported in the row's two masks, they are normalized, and
the pair has genuine Knill--Laflamme distance three.  No moment equation is
assumed; the two families of them are consequences of `hdist`. -/
theorem realFeasible_weightOf (pair : FiberPair) (c d : SS.State 6 ℂ)
    (hc : ∀ x : Word6, c (wordBitString x) ≠ 0 → InMask pair.mask0 x)
    (hd : ∀ x : Word6, d (wordBitString x) ≠ 0 → InMask pair.mask1 x)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    RealFeasible pair (weightOf pair c d) := by
  have hc0 := eq_zero_of_not_mem_fiberSet hc
  have hd0 := eq_zero_of_not_mem_fiberSet hd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro (x | y) <;> exact Complex.normSq_nonneg _
  · have h := SixQubit.massOn_eq_one (fiberSet pair.mask0) c hc0 hnc
    rw [SixQubit.massOn] at h
    rw [← h, sum_fiberSet]
    rfl
  · have h := SixQubit.massOn_eq_one (fiberSet pair.mask1) d hd0 hnd
    rw [SixQubit.massOn] at h
    rw [← h, sum_fiberSet]
    rfl
  · intro j
    have hocc := SixQubit.occOn_eq_of_hasDistance (fiberSet pair.mask0)
      (fiberSet pair.mask1) c d hc0 hd0 hnc hnd hdist j
    show ∑ x : LeftFiber pair,
        weightOf pair c d (Sum.inl x) * coord (leftPoint pair x) j
      = ∑ y : RightFiber pair,
        weightOf pair c d (Sum.inr y) * coord (rightPoint pair y) j
    rw [show (∑ x : LeftFiber pair,
        weightOf pair c d (Sum.inl x) * coord (leftPoint pair x) j)
      = SixQubit.occOn (fiberSet pair.mask0) c j from
        sum_coord_eq_occOn pair.mask0 c j,
      show (∑ y : RightFiber pair,
        weightOf pair c d (Sum.inr y) * coord (rightPoint pair y) j)
      = SixQubit.occOn (fiberSet pair.mask1) d j from
        sum_coord_eq_occOn pair.mask1 d j]
    exact hocc
  · intro jk
    have hocc := SixQubit.occ2On_eq_of_hasDistance (fiberSet pair.mask0)
      (fiberSet pair.mask1) c d hc0 hd0 hnc hnd hdist jk.1.1 jk.1.2
    show ∑ x : LeftFiber pair,
        weightOf pair c d (Sum.inl x) * coord (leftPoint pair x) jk.1.1
          * coord (leftPoint pair x) jk.1.2
      = ∑ y : RightFiber pair,
        weightOf pair c d (Sum.inr y) * coord (rightPoint pair y) jk.1.1
          * coord (rightPoint pair y) jk.1.2
    rw [show (∑ x : LeftFiber pair,
        weightOf pair c d (Sum.inl x) * coord (leftPoint pair x) jk.1.1
          * coord (leftPoint pair x) jk.1.2)
      = SixQubit.occ2On (fiberSet pair.mask0) c jk.1.1 jk.1.2 from
        sum_coord2_eq_occ2On pair.mask0 c jk.1.1 jk.1.2,
      show (∑ y : RightFiber pair,
        weightOf pair c d (Sum.inr y) * coord (rightPoint pair y) jk.1.1
          * coord (rightPoint pair y) jk.1.2)
      = SixQubit.occ2On (fiberSet pair.mask1) d jk.1.1 jk.1.2 from
        sum_coord2_eq_occ2On pair.mask1 d jk.1.1 jk.1.2]
    exact hocc

/-- The existential form the coarse-filter soundness layer consumes. -/
theorem exists_realFeasible (pair : FiberPair) (c d : SS.State 6 ℂ)
    (hc : ∀ x : Word6, c (wordBitString x) ≠ 0 → InMask pair.mask0 x)
    (hd : ∀ x : Word6, d (wordBitString x) ≠ 0 → InMask pair.mask1 x)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    ∃ w : RealWeight pair, RealFeasible pair w :=
  ⟨weightOf pair c d, realFeasible_weightOf pair c d hc hd hnc hnd hdist⟩

end MainTheory.CodeMomentPoint
