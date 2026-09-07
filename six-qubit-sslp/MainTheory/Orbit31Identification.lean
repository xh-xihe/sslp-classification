import MainTheory.Generated.FiniteRankDataShard67
import MainTheory.OuterCompleteness
import SixQubit.Orbit31
import SixQubit.Orbit31MomentRank
import SixQubit.Orbit31MomentPolytope
import MainTheory.FiniteMomentLP

/-!
# The orbit-31 hand certificate and the pipeline pair are the same fibres

Orbit 31's LP affine dimension is certified twice by routes that never meet.
`SixQubit.Orbit31.momentPolytope_affine_dimension` computes it as `9` on the
thirty-two-coordinate normal form of the hand certificate, and
`Generated.OrbitTableSemantics31.lp_affine_dimension` computes it as `9` on
the full-fibre polytope of the pipeline pair `pair67`.  They agree
numerically, and until now nothing said they were about the same object: two
independent certifications rather than one, which is weaker than it looks,
since a coincidence of numbers is not an identification.

This file supplies the identification at the level that matters first -- the
fibres.  The hand certificate's two sixteen-element word sets `S0` and `S1`
are *exactly* the two masks of `pair67`, under the pipeline's own word
encoding `wordBitString w = fun i => w.1.testBit i`.  So the two arguments do
constrain the same pair of computational-basis supports, and orbit 31 is one
orbit rather than two objects that happen to share a number.

The second half is `mem_polytope_iff`: a real point of the pipeline's
full-fibre polytope for `pair67` -- a set of `LabeledWord -> R` with
ninety-six forced-zero coordinates -- is exactly a point supported on the
fibre pair whose restriction along `col` lies in the hand certificate's
thirty-two-coordinate `momentPolytope`.  So the two dimension theorems are two
readings of one polytope, not two certifications that agree on the number `9`.

`col` is *not* the order-preserving enumeration of each mask.  The hand
certificate lists its first fibre as `0, 48, 40, 24, ...`, while the
pipeline's own `OrbitTableRank31.columns` enumerates each mask in increasing
order; the two differ by a column permutation.  `col` is therefore given in
the hand certificate's order and matched against its matrix directly, rather
than routed through the pipeline's enumeration.  `matrixZ_col` is the check
that makes this an identification rather than an assertion: all 736 entries of
the hand-written `23 x 32` table are the pipeline's `entryZ` at the
corresponding fibre column.
-/

namespace MainTheory.Orbit31Identification

open MainTheory.OuterCompleteness

set_option maxRecDepth 100000

/-- **The hand certificate's first fibre is the pipeline mask.** -/
theorem fibre0 (w : FinitePipeline.Word6) :
    FinitePipeline.InMask
        MainTheory.Generated.FiniteRankDataShard67.pair67.mask0 w ↔
      wordBitString w ∈ SixQubit.Orbit31.S0 := by
  revert w
  decide

/-- **The hand certificate's second fibre is the other pipeline mask.** -/
theorem fibre1 (w : FinitePipeline.Word6) :
    FinitePipeline.InMask
        MainTheory.Generated.FiniteRankDataShard67.pair67.mask1 w ↔
      wordBitString w ∈ SixQubit.Orbit31.S1 := by
  revert w
  decide

/-- **The two presentations of orbit 31 carry the same fibre pair.**

Neither mask is the other's: the two sixteen-element supports are distinct, so
this is an identification and not a relabelling that could have matched either
way. -/
theorem same_fibre_pair :
    (∀ w : FinitePipeline.Word6,
        FinitePipeline.InMask
          MainTheory.Generated.FiniteRankDataShard67.pair67.mask0 w ↔
        wordBitString w ∈ SixQubit.Orbit31.S0) ∧
    (∀ w : FinitePipeline.Word6,
        FinitePipeline.InMask
          MainTheory.Generated.FiniteRankDataShard67.pair67.mask1 w ↔
        wordBitString w ∈ SixQubit.Orbit31.S1) ∧
    MainTheory.Generated.FiniteRankDataShard67.pair67.mask0 ≠
      MainTheory.Generated.FiniteRankDataShard67.pair67.mask1 :=
  ⟨fibre0, fibre1, by decide⟩


/-! ## The two moment systems are one system -/

open MainTheory.FiniteMomentMatrix in
/-- The thirty-two fibre columns, in the hand certificate's own order.

In the hand certificate's own order, not the increasing enumeration; see the
module header. -/
def col : Fin 32 → LabeledWord :=
  ![(false, 0), (false, 48), (false, 40), (false, 24), (false, 38), (false, 22),
    (false, 14), (false, 62), (false, 37), (false, 21), (false, 13), (false, 61),
    (false, 35), (false, 19), (false, 11), (false, 59),
    (true, 4), (true, 52), (true, 44), (true, 28), (true, 2), (true, 50),
    (true, 42), (true, 26), (true, 1), (true, 49), (true, 41), (true, 25),
    (true, 39), (true, 23), (true, 15), (true, 63)]

theorem col_injective : Function.Injective col := by decide

/-- **The columns are exactly the fibre pair.** -/
theorem inFiber_iff (c : MainTheory.FiniteMomentMatrix.LabeledWord) :
    MainTheory.FiniteMomentLP.InFiber
        MainTheory.Generated.FiniteRankDataShard67.pair67 c ↔ ∃ j, col j = c := by
  revert c
  decide

set_option maxHeartbeats 2000000 in
/-- **The hand certificate's moment matrix is the pipeline's, restricted.**

`SixQubit.Orbit31.momentMatrixZ` was written out by hand as a `23 x 32` table;
this says every one of its 736 entries is the pipeline's `entryZ` at the
corresponding fibre column. -/
theorem matrixZ_col :
    MainTheory.FiniteMomentMatrix.matrixZ col = SixQubit.Orbit31.momentMatrixZ := by
  funext r j
  revert r j
  decide

set_option maxHeartbeats 1000000 in
private theorem sum_over_col (p : MainTheory.FiniteMomentMatrix.LabeledWord → ℝ)
    (hp : ∀ c, ¬ MainTheory.FiniteMomentLP.InFiber
      MainTheory.Generated.FiniteRankDataShard67.pair67 c → p c = 0)
    (f : MainTheory.FiniteMomentMatrix.LabeledWord → ℝ) :
    ∑ c, f c * p c = ∑ j : Fin 32, f (col j) * p (col j) := by
  have h1 : ∑ c ∈ Finset.univ.image col, f c * p c
      = ∑ j : Fin 32, f (col j) * p (col j) :=
    Finset.sum_image (fun x _ y _ h => col_injective h)
  rw [← h1]
  refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro c _ hc
  have hout : ¬ MainTheory.FiniteMomentLP.InFiber
      MainTheory.Generated.FiniteRankDataShard67.pair67 c := by
    rw [inFiber_iff]
    rintro ⟨j, hj⟩
    exact hc (Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩)
  rw [hp c hout, mul_zero]


private theorem rhsQ_eq (r : Fin 23) :
    MainTheory.FiniteMomentMatrix.rhsQ r = if (r : ℕ) < 2 then 1 else 0 := by
  revert r
  decide

private theorem rhs_agree (r : Fin 23) :
    ((MainTheory.FiniteMomentMatrix.rhsQ r : ℚ) : ℝ)
      = SixQubit.Orbit31.momentRhs r := by
  rw [rhsQ_eq]
  fin_cases r <;> norm_num [SixQubit.Orbit31.momentRhs]

private theorem moment_row_real
    (p : MainTheory.FiniteMomentMatrix.LabeledWord → ℝ) (r : Fin 23) :
    ((MainTheory.FiniteMomentLP.fullMatrixQ
        MainTheory.Generated.FiniteRankDataShard67.pair67).map
        (algebraMap ℚ ℝ)).mulVec p (Sum.inl r)
      = ∑ c, ((MainTheory.FiniteMomentMatrix.entryZ r c : ℚ) : ℝ) * p c := by
  simp [Matrix.mulVec, dotProduct, MainTheory.FiniteMomentLP.fullMatrixQ,
    Matrix.map_apply]

private theorem support_row_real
    (p : MainTheory.FiniteMomentMatrix.LabeledWord → ℝ)
    (x : MainTheory.FiniteMomentMatrix.LabeledWord) :
    ((MainTheory.FiniteMomentLP.fullMatrixQ
        MainTheory.Generated.FiniteRankDataShard67.pair67).map
        (algebraMap ℚ ℝ)).mulVec p (Sum.inr x)
      = if MainTheory.FiniteMomentLP.InFiber
          MainTheory.Generated.FiniteRankDataShard67.pair67 x then 0 else p x := by
  by_cases hx : MainTheory.FiniteMomentLP.InFiber
      MainTheory.Generated.FiniteRankDataShard67.pair67 x <;>
    simp [Matrix.mulVec, dotProduct, MainTheory.FiniteMomentLP.fullMatrixQ,
      Matrix.map_apply, hx]

/-- **The two moment systems are the same system.**

A real point of the pipeline's full-fibre polytope for `pair67` is exactly a
point supported on the fibre pair whose restriction along `col` lies in the
hand certificate's thirty-two-coordinate moment polytope.

This is the transport the header said was missing.  With it the two affine
dimension theorems -- `SixQubit.Orbit31.momentPolytope_affine_dimension` and
`Generated.OrbitTableSemantics31.lp_affine_dimension` -- are two readings of
one polytope rather than two independent certifications that happen to agree
on the number `9`. -/
theorem mem_polytope_iff (p : MainTheory.FiniteMomentMatrix.LabeledWord → ℝ) :
    p ∈ MainTheory.FiniteMomentLP.polytope
        MainTheory.Generated.FiniteRankDataShard67.pair67 ↔
      (∀ c, ¬ MainTheory.FiniteMomentLP.InFiber
          MainTheory.Generated.FiniteRankDataShard67.pair67 c → p c = 0) ∧
      (fun j => p (col j)) ∈ SixQubit.Orbit31.momentPolytope := by
  constructor
  · rintro ⟨heq, hnn⟩
    have hsupp : ∀ c, ¬ MainTheory.FiniteMomentLP.InFiber
        MainTheory.Generated.FiniteRankDataShard67.pair67 c → p c = 0 := by
      intro c hc
      have h := congrFun heq (Sum.inr c)
      rw [support_row_real p c, if_neg hc] at h
      simpa [MainTheory.FiniteMomentLP.fullRhsQ] using h
    refine ⟨hsupp, ?_, fun j => hnn (col j)⟩
    funext r
    have h := congrFun heq (Sum.inl r)
    rw [moment_row_real p r] at h
    rw [Matrix.mulVec, dotProduct]
    have hcol := congrFun (congrFun matrixZ_col r)
    calc ∑ j : Fin 32, SixQubit.Orbit31.momentMatrix r j * p (col j)
        = ∑ j : Fin 32,
            ((MainTheory.FiniteMomentMatrix.entryZ r (col j) : ℚ) : ℝ) * p (col j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [SixQubit.Orbit31.momentMatrix, Matrix.map_apply, ← hcol j]
          norm_num [MainTheory.FiniteMomentMatrix.matrixZ]
      _ = ∑ c, ((MainTheory.FiniteMomentMatrix.entryZ r c : ℚ) : ℝ) * p c :=
          (sum_over_col p hsupp
            (fun c => ((MainTheory.FiniteMomentMatrix.entryZ r c : ℚ) : ℝ))).symm
      _ = SixQubit.Orbit31.momentRhs r := by
          rw [h]
          simpa [MainTheory.FiniteMomentLP.fullRhsQ] using rhs_agree r
  · rintro ⟨hsupp, heq, hnn⟩
    refine ⟨?_, ?_⟩
    · funext r
      cases r with
      | inl r =>
          rw [moment_row_real p r, sum_over_col p hsupp]
          have hcol := congrFun (congrFun matrixZ_col r)
          have hr := congrFun heq r
          rw [Matrix.mulVec, dotProduct] at hr
          calc ∑ j : Fin 32,
                ((MainTheory.FiniteMomentMatrix.entryZ r (col j) : ℚ) : ℝ) * p (col j)
              = ∑ j : Fin 32, SixQubit.Orbit31.momentMatrix r j * p (col j) := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [SixQubit.Orbit31.momentMatrix, Matrix.map_apply, ← hcol j]
                norm_num [MainTheory.FiniteMomentMatrix.matrixZ]
            _ = SixQubit.Orbit31.momentRhs r := hr
            _ = _ := by
                simpa [MainTheory.FiniteMomentLP.fullRhsQ] using (rhs_agree r).symm
      | inr x =>
          rw [support_row_real p x]
          by_cases hx : MainTheory.FiniteMomentLP.InFiber
              MainTheory.Generated.FiniteRankDataShard67.pair67 x
          · simp [hx, MainTheory.FiniteMomentLP.fullRhsQ]
          · simp [hx, hsupp x hx, MainTheory.FiniteMomentLP.fullRhsQ]
    · intro c
      by_cases hc : MainTheory.FiniteMomentLP.InFiber
          MainTheory.Generated.FiniteRankDataShard67.pair67 c
      · obtain ⟨j, rfl⟩ := (inFiber_iff c).1 hc
        exact hnn j
      · rw [hsupp c hc]

end MainTheory.Orbit31Identification
