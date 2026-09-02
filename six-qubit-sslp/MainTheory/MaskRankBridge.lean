import MainTheory.AffineRankCertificate
import MainTheory.OuterCompleteness
import MainTheory.CodeAffineSpanBridge

/-!
# Affine rank versus linear rank of a residue mask

The coarse filter is stated with `AffineRankCertificate.maskAffineRank`, the
`ℚ`-affine rank of the Boolean points a mask selects.  Everything that
produces a rank from an actual code -- `SixQubitSemanticEntrance.SupportedBitBasis`,
and through it the binary minor of the distance-three rationalization --
produces instead the `ℝ`-*linear* rank of the raw bit vectors of a support.
The two notions differ by at most one, and by exactly one when the origin is
outside the affine span, so identifying them is not a formality.

For the **zero-residue mask** the gap closes outright, and this file is that
observation: the all-zero word has subset sum zero, so it lies in the residue-
zero fibre of every record, so the origin is one of the mask's own points, so
the affine span passes through the origin and its direction is the plain linear
span.  `residueZeroMask_affineRank_eq_span` is the statement.

That is one of the two halves the coarse-filter entry needs.  The other -- the
`q/m` residue mask, whose fibre does not contain the origin -- does not close
this way and is left alone here rather than papered over.
-/

namespace MainTheory.MaskRankBridge

open MainTheory.AffineRankCertificate
open MainTheory.FinitePipeline

/-! ## The origin as a mask point -/

/-- The Boolean point of the zero word is the origin. -/
@[simp] theorem point_zero : point (0 : Word6) = (0 : Vec6) := by
  funext j
  simp [point]

/-- A mask containing the zero word has the origin among its points. -/
theorem zero_mem_maskPointSet {mask : ℕ} (h : InMask mask (0 : Word6)) :
    (0 : Vec6) ∈ maskPointSet mask := by
  refine ⟨(0 : Word6), h, ?_⟩
  exact point_zero

/-! ## Affine rank through the origin -/

/-- **A mask whose point set contains the origin has affine rank equal to the
rank of its linear span.**

`vectorSpan` is the span of the differences from any chosen point of the set;
choosing the origin makes those differences the points themselves. -/
theorem maskAffineRank_eq_finrank_span {mask : ℕ} (h : InMask mask (0 : Word6)) :
    maskAffineRank mask =
      Module.finrank ℚ (Submodule.span ℚ (maskPointSet mask)) := by
  have h0 : (0 : Vec6) ∈ maskPointSet mask := zero_mem_maskPointSet h
  have hset : (fun p => p -ᵥ (0 : Vec6)) '' maskPointSet mask
      = maskPointSet mask := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨v, hv, by simp⟩
  unfold maskAffineRank
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℚ h0, hset]

/-! ## The zero-residue fibre of an enumerated record -/

open MainTheory.OuterCompleteness

/-- The all-zero word has subset sum zero, hence lies in every record's
zero-residue fibre. -/
theorem zero_inMask_residueZero (r : OuterEnumeration.RawRecord) :
    InMask (recordFiberPair r).mask0 (0 : Word6) := by
  rw [in_recordFiberPair_mask0_iff]
  have hsum : OuterEnumeration.subsetSum r.a (0 : Word6).1 = 0 := by
    simp [OuterEnumeration.subsetSum]
  rw [hsum]
  exact Nat.zero_mod r.q

/-- **The zero-residue mask of an enumerated record has affine rank equal to
the rank of its linear span.**

This is the half of the coarse filter's rank hypothesis that the raw-bit
rationalization can meet directly: a bound proved against the `ℝ`-linear rank
of a support inside this fibre is a bound against the fibre's own affine
rank, with no off-by-one to absorb. -/
theorem residueZeroMask_affineRank_eq_span (r : OuterEnumeration.RawRecord) :
    maskAffineRank (recordFiberPair r).mask0 =
      Module.finrank ℚ
        (Submodule.span ℚ (maskPointSet (recordFiberPair r).mask0)) :=
  maskAffineRank_eq_finrank_span (zero_inMask_residueZero r)

/-! ## From a real supported basis to the rational affine rank

`SixQubitSemanticEntrance.SupportedBitBasis` hands out an `ℝ`-linearly
independent family of Boolean points inside a state's actual support.  The
coarse filter counts rank over `ℚ`.  Mathlib has no rank transfer between the
two fields in either direction for matrices, but it does have the *descending*
direction for linear independence, and that is the one needed here: an
`ℝ`-independent family is `ℚ`-independent, and independence is reflected by
the injective `ℚ`-linear coordinatewise cast, so the same words are
independent as rational points.
-/

open MainTheory.CodeAffineSpanBridge in
/-- The coordinatewise cast of rational six-vectors into real ones. -/
def toReal : Vec6 →ₗ[ℚ] (Fin 6 → ℝ) where
  toFun v := fun j => (v j : ℝ)
  map_add' u v := by funext j; simp
  map_smul' a v := by funext j; simp [Rat.smul_def]

@[simp] theorem toReal_apply (v : Vec6) (j : Fin 6) :
    toReal v j = (v j : ℝ) := rfl

theorem toReal_injective : Function.Injective toReal := by
  intro u v h
  funext j
  have hj : ((u j : ℝ)) = ((v j : ℝ)) := congrFun h j
  exact_mod_cast hj

/-- The rational Boolean point casts to the real one. -/
theorem toReal_point (x : Word6) :
    toReal (point x) =
      MainTheory.CodeAffineSpanBridge.bitPoint
        (MainTheory.OuterCompleteness.wordBitString x) := by
  funext j
  by_cases hb : x.1.testBit j.1 <;>
    simp [point, MainTheory.FinitePipeline.bit,
      MainTheory.CodeAffineSpanBridge.bitPoint,
      MainTheory.OuterCompleteness.wordBitString, hb]

/-- **Real independence of the Boolean points descends to rational
independence.** -/
theorem linearIndependent_point_of_real {r : ℕ} (w : Fin r → Word6)
    (h : LinearIndependent ℝ (fun i =>
      MainTheory.CodeAffineSpanBridge.bitPoint
        (MainTheory.OuterCompleteness.wordBitString (w i)))) :
    LinearIndependent ℚ (fun i => point (w i)) := by
  have hQ : LinearIndependent ℚ (fun i =>
      MainTheory.CodeAffineSpanBridge.bitPoint
        (MainTheory.OuterCompleteness.wordBitString (w i))) :=
    h.restrict_scalars' ℚ
  refine LinearIndependent.of_comp toReal ?_
  have : (toReal ∘ fun i => point (w i)) = fun i =>
      MainTheory.CodeAffineSpanBridge.bitPoint
        (MainTheory.OuterCompleteness.wordBitString (w i)) := by
    funext i
    exact toReal_point (w i)
  rw [this]
  exact hQ

/-- **An independent family of points inside a mask bounds the mask's rank.** -/
theorem card_le_finrank_span_of_subset {r : ℕ} {mask : ℕ} (w : Fin r → Word6)
    (hmem : ∀ i, InMask mask (w i))
    (hind : LinearIndependent ℚ (fun i => point (w i))) :
    r ≤ Module.finrank ℚ (Submodule.span ℚ (maskPointSet mask)) := by
  have hsub : Set.range (fun i => point (w i)) ⊆ maskPointSet mask := by
    rintro _ ⟨i, rfl⟩
    exact ⟨w i, hmem i, rfl⟩
  have hcard : Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun i => point (w i)))) = r := by
    rw [finrank_span_eq_card hind]
    simp
  calc r = Module.finrank ℚ
        (Submodule.span ℚ (Set.range (fun i => point (w i)))) := hcard.symm
    _ ≤ Module.finrank ℚ (Submodule.span ℚ (maskPointSet mask)) :=
        Submodule.finrank_mono (Submodule.span_mono hsub)

/-- **The geometric half of the coarse filter, for the zero-residue fibre.**

If a state's support contains `r` words whose real Boolean points are linearly
independent, and every one of them lies in a record's zero-residue fibre, then
that fibre's affine rank -- the number the coarse filter compares against
`rMin q` -- is at least `r`.

The zero-residue fibre is the one where this closes: it contains the all-zero
word, so its affine and linear ranks agree, and a *linear* independence
statement about the support suffices.  The `q/m` fibre does not contain the
origin, and there the same argument yields only `r - 1`; closing that half
needs the paper's bound at the **affine** rank of the support
(`six:eq:ractual` with `six:eq:qbetar`), which is strictly stronger than the
linear-rank bound this development proves. -/
theorem le_maskAffineRank_mask0 {r : ℕ} (rec : OuterEnumeration.RawRecord)
    (w : Fin r → Word6)
    (hmem : ∀ i, InMask (recordFiberPair rec).mask0 (w i))
    (hind : LinearIndependent ℝ (fun i =>
      MainTheory.CodeAffineSpanBridge.bitPoint
        (MainTheory.OuterCompleteness.wordBitString (w i)))) :
    r ≤ maskAffineRank (recordFiberPair rec).mask0 := by
  rw [residueZeroMask_affineRank_eq_span rec]
  exact card_le_finrank_span_of_subset w hmem
    (linearIndependent_point_of_real w hind)

end MainTheory.MaskRankBridge
