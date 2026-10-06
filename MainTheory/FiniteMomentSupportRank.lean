import MainTheory.FiniteMomentLP
import MainTheory.MomentModelBridge
import MainTheory.LPActiveDimension

namespace MainTheory.FiniteMomentSupportRank

open MainTheory.FiniteMomentLP MainTheory.FiniteMomentMatrix
open MainTheory.MomentModelBridge.RankCast

noncomputable section

def supportPoints (p : LabeledWord → ℝ) (b : Bool) : Set (Fin 6 → ℝ) :=
  realPoint '' {x | 0 < p (b, x)}

def supportRank (p : LabeledWord → ℝ) (b : Bool) : ℕ :=
  MainTheory.ActiveFace.affineRank (supportPoints p b)

def faceRank (face : MainTheory.FinitePipeline.FaceData) (b : Bool) : ℕ :=
  realMaskAffineRank (if b then face.active1 else face.active0)

theorem supportRank_le (pair : FP) (face : MainTheory.FinitePipeline.FaceData)
    (hf : face.Valid pair) (p : LabeledWord → ℝ) (hp : p ∈ polytope pair) (b : Bool) :
    supportRank p b ≤ faceRank face b := by
  apply Submodule.finrank_mono
  apply AffineSubspace.direction_le
  apply affineSpan_mono
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, (active_real_iff pair face hf (b, x)).mp ⟨p, hp, hx⟩, rfl⟩

/-- A single real feasible point attains both complete active supports. -/
theorem exists_attains_both (pair : FP) (face : MainTheory.FinitePipeline.FaceData)
    (hf : face.Valid pair) : ∃ p ∈ polytope pair, ∀ b, supportRank p b = faceRank face b := by
  obtain ⟨p, hp, hpos⟩ := MainTheory.ActiveFace.exists_positive_iff_active (polytope pair)
    (MainTheory.LPDimension.feasibleSet_convex _ _) (polytope_nonempty pair face hf)
    (fun _ h => h.2)
  refine ⟨p, hp, fun b => ?_⟩
  have hs : supportPoints p b = realMaskPointSet (if b then face.active1 else face.active0) := by
    apply congrArg (Set.image realPoint)
    ext x
    exact (hpos (b, x)).trans (active_real_iff pair face hf (b, x))
  exact congrArg MainTheory.ActiveFace.affineRank hs

/-- Maximum attainable support rank is exactly the active-face rank; all
weights range over the full real nonnegative LP, including forced zeros. -/
theorem rank_threshold_iff (pair : FP) (face : MainTheory.FinitePipeline.FaceData)
    (hf : face.Valid pair) (r : ℕ) :
    (∃ p ∈ polytope pair, r ≤ min (supportRank p false) (supportRank p true)) ↔
      r ≤ min (faceRank face false) (faceRank face true) := by
  constructor
  · rintro ⟨p, hp, hr⟩
    exact hr.trans (min_le_min (supportRank_le pair face hf p hp false)
      (supportRank_le pair face hf p hp true))
  · intro hr
    obtain ⟨p, hp, he⟩ := exists_attains_both pair face hf
    exact ⟨p, hp, by simpa only [he] using hr⟩

end

end MainTheory.FiniteMomentSupportRank
