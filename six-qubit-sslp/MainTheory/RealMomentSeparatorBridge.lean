import MainTheory.MomentModelBridge

/-!
# Exact rational separators exclude real fibre moment polytopes

The generated infeasibility certificates have rational coefficients, whereas
the moment polytope in `main.tex` allows arbitrary real probabilities.  A
reverse rationality assumption on those probabilities would therefore be too
strong.  This file instead casts only the separator and runs its expectation
argument directly over `ℝ`.

The two index types below are the *actual* residue fibres.  Thus no weight on a
point outside the advertised `FiberPair` can enter the real problem.
-/

namespace MainTheory.RealMomentSeparatorBridge

open scoped BigOperators
open MainTheory.FinitePipeline
open MainTheory.MomentPolytope
open MainTheory.MomentModelBridge.PipelineToPolytope

/-- The left and right finite sets of Boolean words advertised by a pair. -/
abbrev LeftFiber (pair : FiberPair) :=
  {x : Word6 // InMask pair.mask0 x}

abbrev RightFiber (pair : FiberPair) :=
  {x : Word6 // InMask pair.mask1 x}

def leftPoint (pair : FiberPair) : LeftFiber pair → BitPoint6 :=
  fun x => wordPoint x.1

def rightPoint (pair : FiberPair) : RightFiber pair → BitPoint6 :=
  fun x => wordPoint x.1

/-- The paper-facing real moment problem on exactly the two declared fibres. -/
abbrev RealWeight (pair : FiberPair) :=
  Sum (LeftFiber pair) (RightFiber pair) → ℝ

def RealFeasible (pair : FiberPair) (p : RealWeight pair) : Prop :=
  MainTheory.MomentPolytope.Feasible (leftPoint pair) (rightPoint pair) p

/-- A rational score evaluated in `ℝ`; only the certificate is cast. -/
def realScore (h : Fin 21 → ℚ) (x : Word6) : ℝ :=
  (score h x : ℝ)

private def realScoreSum (h : Fin 21 → ℚ) (x : Word6) : ℝ :=
  ∑ k, (h k : ℝ) * (feature x k : ℝ)

private theorem realScore_eq_realScoreSum (h : Fin 21 → ℚ) (x : Word6) :
    realScore h x = realScoreSum h x := by
  unfold realScore realScoreSum
  rw [score_eq_scoreSum]
  unfold scoreSum
  rw [Rat.cast_sum]
  simp only [Rat.cast_mul]

/-- Pointwise identification of a cast pipeline pair-feature with the product
of the corresponding real Boolean coordinates.  Keeping this lemma separate
avoids asking `simp` to normalize the nested `if` implementation of `feature`.
-/
private theorem cast_feature_pair (j l : Fin 6) (hjl : j < l) (x : Word6) :
    (feature x (pairIndex j l) : ℝ) =
      coord (wordPoint x) j * coord (wordPoint x) l := by
  rw [feature_pair x j l hjl, Rat.cast_mul,
    coord_wordPoint, coord_wordPoint]

/-- The real moment equations imply equality for every one of the pipeline's
21 feature coordinates. -/
private theorem real_feature_moment_eq {pair : FiberPair}
    {p : RealWeight pair} (hp : RealFeasible pair p) (k : Fin 21) :
    (∑ x : LeftFiber pair, p (Sum.inl x) * (feature x.1 k : ℝ)) =
      ∑ x : RightFiber pair, p (Sum.inr x) * (feature x.1 k : ℝ) := by
  obtain ⟨r, rfl⟩ := rowIndex_surjective k
  rcases r with j | ⟨⟨j, l⟩, hjl⟩
  · simpa [RealFeasible, leftPoint, rightPoint, mean0, mean1,
      rowIndex, feature_single, coord_wordPoint] using hp.firstMoment j
  · simpa [RealFeasible, leftPoint, rightPoint, second0, second1,
      rowIndex, cast_feature_pair j l hjl, mul_assoc] using
      hp.secondMoment ⟨⟨j, l⟩, hjl⟩

/-- Equal real degree-two moments give equal expected value to the cast of
every rational linear functional used by a separator. -/
theorem expected_realScore_eq {pair : FiberPair} {p : RealWeight pair}
    (hp : RealFeasible pair p) (h : Fin 21 → ℚ) :
    (∑ x : LeftFiber pair, p (Sum.inl x) * realScore h x.1) =
      ∑ x : RightFiber pair, p (Sum.inr x) * realScore h x.1 := by
  simp_rw [realScore_eq_realScoreSum]
  calc
    (∑ x : LeftFiber pair, p (Sum.inl x) * realScoreSum h x.1) =
        ∑ k, (h k : ℝ) *
          (∑ x : LeftFiber pair,
            p (Sum.inl x) * (feature x.1 k : ℝ)) := by
      simp only [realScoreSum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ k, (h k : ℝ) *
          (∑ x : RightFiber pair,
            p (Sum.inr x) * (feature x.1 k : ℝ)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [real_feature_moment_eq hp k]
    _ = ∑ x : RightFiber pair,
          p (Sum.inr x) * realScoreSum h x.1 := by
      simp only [realScoreSum, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro k _
      ring

private theorem left_expectation_le {pair : FiberPair} {p : RealWeight pair}
    (hp : RealFeasible pair p) (cert : SeparatorCertificate pair) :
    (∑ x : LeftFiber pair,
      p (Sum.inl x) * realScore cert.h x.1) ≤ (cert.lower : ℝ) := by
  calc
    (∑ x : LeftFiber pair,
        p (Sum.inl x) * realScore cert.h x.1) ≤
        ∑ x : LeftFiber pair, p (Sum.inl x) * (cert.lower : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      have hb : realScore cert.h x.1 ≤ (cert.lower : ℝ) := by
        change (score cert.h x.1 : ℝ) ≤ (cert.lower : ℝ)
        exact_mod_cast cert.left_bound x.1 x.2
      exact mul_le_mul_of_nonneg_left hb (hp.nonneg (Sum.inl x))
    _ = (cert.lower : ℝ) := by
      rw [← Finset.sum_mul, hp.norm0, one_mul]

private theorem right_expectation_ge {pair : FiberPair} {p : RealWeight pair}
    (hp : RealFeasible pair p) (cert : SeparatorCertificate pair) :
    (cert.upper : ℝ) ≤
      ∑ x : RightFiber pair,
        p (Sum.inr x) * realScore cert.h x.1 := by
  calc
    (cert.upper : ℝ) =
        ∑ x : RightFiber pair, p (Sum.inr x) * (cert.upper : ℝ) := by
      rw [← Finset.sum_mul, hp.norm1, one_mul]
    _ ≤ ∑ x : RightFiber pair,
        p (Sum.inr x) * realScore cert.h x.1 := by
      apply Finset.sum_le_sum
      intro x _
      have hb : (cert.upper : ℝ) ≤ realScore cert.h x.1 := by
        change (cert.upper : ℝ) ≤ (score cert.h x.1 : ℝ)
        exact_mod_cast cert.right_bound x.1 x.2
      exact mul_le_mul_of_nonneg_left hb (hp.nonneg (Sum.inr x))

/-- **A valid rational separator rules out arbitrary real probabilities on
the advertised fibres.**  No rational lift of the probabilities is assumed. -/
theorem not_realFeasible_of_separator {pair : FiberPair}
    (cert : SeparatorCertificate pair) :
    ¬ ∃ p : RealWeight pair, RealFeasible pair p := by
  rintro ⟨p, hp⟩
  have hleft := left_expectation_le hp cert
  have hright := right_expectation_ge hp cert
  have heq := expected_realScore_eq hp cert.h
  have hgap : (cert.lower : ℝ) < (cert.upper : ℝ) := by
    exact_mod_cast cert.gap
  linarith

/-- Stored sparse separator payloads inherit the real-infeasibility theorem. -/
theorem not_realFeasible_of_separatorData {pair : FiberPair}
    {data : SeparatorData} (h : data.Valid pair) :
    ¬ ∃ p : RealWeight pair, RealFeasible pair p :=
  not_realFeasible_of_separator (data.certificate pair h)

/-- Row-level form used by generated moment directories: whenever the stored
Boolean says `false`, its kernel-checked payload excludes the real fibre LP. -/
theorem CertifiedMomentRow.not_realFeasible (row : CertifiedMomentRow)
    (hfalse : row.result.isFeasible = false) :
    ¬ ∃ p : RealWeight row.pair, RealFeasible row.pair p := by
  cases hresult : row.result with
  | feasible pairId primal =>
      simp [hresult, MomentResultData.isFeasible] at hfalse
  | infeasible pairId separator =>
      apply not_realFeasible_of_separatorData
      simpa [hresult, MomentResultData.ValidFor] using row.valid

end MainTheory.RealMomentSeparatorBridge
