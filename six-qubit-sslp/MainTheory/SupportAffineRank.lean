import MainTheory.SortedPivotConstruction
import MainTheory.CodeActiveFace
import MainTheory.RankThresholdBridge

/-!
# `q <= beta_r` at the affine rank of the actual support

`thm:d3-bound` bounds the modulus by `beta_r` where `r` is the *affine*
dimension of the code's own support, `six:eq:ractual`.  What this development
proved was `q <= beta_n`: the sharper form needed the normalization the paper
opens with, a local `X` conjugation putting `0^n` into `T_0`
(`eq:zero-in-T0`), which makes the common affine span linear so that `r` is
the affine and the linear rank at once.

That normalization is now recorded --
`RankTwoGlobal.TwoFiberCertificate.base_supported`, exported by
`SortedPivotConstruction.exists_normalForm_pivot_full` as
`S.frame.vec 0 0 != 0` -- and it is exactly what closes the gap.  Without a
supported zero word only `P.rank - 1` difference vectors sit in the affine
direction and one gets `beta_{r+1}`; with it the `P.rank` vertex points
themselves do, and one gets `beta_r`.

What is *not* closed is the other clause of the same theorem, `q | d_r(C)` with
`d_r` the last Smith invariant factor.  The chain
`q | inverseDenominator P.matrix` (`SortedPivot.Pivot.q_dvd_inverseDenominator`)
and `inverseDenominator C = w.lastFactor` is complete, but `w` is a
`SharpClearing.SmithWitness` and nothing in the repository or in Mathlib can
build one for these matrices; `Clearing.lean` records why.
-/

namespace MainTheory.SupportAffineRank

open MainTheory
open MainTheory.MaskRankBridge
open MainTheory.SortedForm
open MainTheory.SortedPivot

variable {C : CodeSpec.ExactCode 6 2 3}

/-! ## The support's affine rank -/

/-- The rational points of a state's actual support. -/
def supportPointSet (c : SS.State 6 ℂ) : Set AffineRankCertificate.Vec6 :=
  qpoint '' {s : SS.BitString 6 | c s ≠ 0}

/-- **The paper's `r`** (`six:eq:ractual`): the affine dimension of the
support of a logical word. -/
noncomputable def supportAffineRank (c : SS.State 6 ℂ) : ℕ :=
  Module.finrank ℚ (affineSpan ℚ (supportPointSet c)).direction

theorem qpoint_zero : qpoint (fun _ => false) = 0 := by
  funext j
  simp [qpoint]

/-- With the zero word supported, the affine span passes through the origin,
so its direction is the ordinary span.  This is `eq:zero-in-T0`. -/
theorem supportAffineRank_eq_finrank_span {c : SS.State 6 ℂ}
    (h : c (fun _ => false) ≠ 0) :
    supportAffineRank c
      = Module.finrank ℚ (Submodule.span ℚ (supportPointSet c)) := by
  have h0 : (0 : AffineRankCertificate.Vec6) ∈ supportPointSet c :=
    ⟨fun _ => false, h, qpoint_zero⟩
  have hset : (fun p => p -ᵥ (0 : AffineRankCertificate.Vec6)) ''
      supportPointSet c = supportPointSet c := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hv
      exact ⟨v, hv, by simp⟩
  unfold supportAffineRank
  rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℚ h0, hset]

/-- Independent supported points bound the span's rank from below. -/
theorem card_le_finrank_supportSpan {r : ℕ} {c : SS.State 6 ℂ}
    (w : Fin r → SS.BitString 6) (hmem : ∀ i, c (w i) ≠ 0)
    (hind : LinearIndependent ℚ (fun i => qpoint (w i))) :
    r ≤ Module.finrank ℚ (Submodule.span ℚ (supportPointSet c)) := by
  have hsub : Set.range (fun i => qpoint (w i)) ⊆ supportPointSet c := by
    rintro _ ⟨i, rfl⟩
    exact ⟨w i, hmem i, rfl⟩
  have hcard : Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun i => qpoint (w i)))) = r := by
    rw [finrank_span_eq_card hind]
    simp
  calc r = Module.finrank ℚ
        (Submodule.span ℚ (Set.range (fun i => qpoint (w i)))) := hcard.symm
    _ ≤ Module.finrank ℚ (Submodule.span ℚ (supportPointSet c)) :=
        Submodule.finrank_mono (Submodule.span_mono hsub)

/-- Six coordinates bound every affine rank here. -/
theorem supportAffineRank_le_six (c : SS.State 6 ℂ) :
    supportAffineRank c ≤ 6 := by
  have h := Submodule.finrank_le (affineSpan ℚ (supportPointSet c)).direction
  simpa [supportAffineRank] using h

/-! ## The bound -/

/-- **The pivot's rank is at most the support's affine rank.**

The pivot's vertices are supported points (`vertex_supported`) and their
rational points are independent, and the zero word is supported, so the affine
span's direction already contains all `P.rank` of them. -/
theorem rank_le_supportAffineRank {S : SortedNormalForm C} (P : Pivot S)
    (hzero : S.frame.vec 0 (fun _ => false) ≠ 0) :
    P.rank ≤ supportAffineRank (S.frame.vec 0) := by
  rw [supportAffineRank_eq_finrank_span hzero]
  exact card_le_finrank_supportSpan P.vertex P.vertex_supported P.linearIndependent

/-- **`q <= beta_r` at the affine rank of the actual support**, which is
`thm:d3-bound`'s `six:eq:qbetar`. -/
theorem q_le_threshold_supportAffineRank {S : SortedNormalForm C} (P : Pivot S)
    (hzero : S.frame.vec 0 (fun _ => false) ≠ 0) :
    S.q ≤ CoarseFilter.threshold (supportAffineRank (S.frame.vec 0)) :=
  (MainTheory.CodeActiveFace.pivot_q_le_threshold P).trans
    (MainTheory.RankThresholdBridge.threshold_mono
      (rank_le_supportAffineRank P hzero)
      (supportAffineRank_le_six _))

/-- **The clause, for every exact `((6,2,3))` code with a projectively
nontrivial diagonal symmetry.**

There is a sorted normal form whose modulus is bounded by the cutoff at the
affine dimension of its own support, not merely at `n`. -/
theorem exists_normalForm_q_le_beta_supportRank
    (C : CodeSpec.ExactCode 6 2 3) (theta : Fin 6 → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ S : SortedNormalForm C,
      S.q ≤ CoarseFilter.threshold (supportAffineRank (S.frame.vec 0)) ∧
      S.q ≤ 9 := by
  obtain ⟨S, P, hq9, hzero, _, _⟩ :=
    MainTheory.SortedPivotConstruction.exists_normalForm_pivot_full C theta hpres hnt
  exact ⟨S, q_le_threshold_supportAffineRank P hzero, hq9⟩

end MainTheory.SupportAffineRank
