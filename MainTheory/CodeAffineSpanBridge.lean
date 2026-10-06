import MainTheory.CodeSpec
import MainTheory.AffineSpan
import MainTheory.Covariance

/-!
# From an exact rank-two code to the common affine span of its actual supports

This file closes the bookkeeping gap between the code-facing occupation-number
lemmas in `MainTheory.AffineSpan` and the geometric theorem
`MainTheory.Covariance.affineSpan_eq_of_cov_eq₂`.

The supports below are the *actual* nonzero supports of the two logical frame
vectors.  Consequently their weights are strictly positive, rather than merely
nonnegative weights on a larger residue fibre.  No spectral decomposition,
finite-lift datum, or binary-Smith bound is assumed or produced here.
-/

namespace MainTheory.CodeAffineSpanBridge

open scoped BigOperators
open MainTheory

noncomputable section

variable {n d : ℕ}

/-! ## Actual supports and their probability distributions -/

/-- The actual computational-basis support of a state. -/
def actualSupport (psi : SS.State n ℂ) : Set (SS.BitString n) :=
  {x | psi x ≠ 0}

/-- A concrete finite enumeration of `actualSupport`. -/
noncomputable def actualSupportFinset (psi : SS.State n ℂ) :
    Finset (SS.BitString n) := by
  classical
  exact Finset.univ.filter fun x => x ∈ actualSupport psi

@[simp] theorem mem_actualSupportFinset (psi : SS.State n ℂ)
    (x : SS.BitString n) :
    x ∈ actualSupportFinset psi ↔ psi x ≠ 0 := by
  classical
  simp [actualSupportFinset, actualSupport]

/-- The finite type indexing exactly the nonzero amplitudes of `psi`. -/
abbrev SupportIndex (psi : SS.State n ℂ) :=
  {x : SS.BitString n // x ∈ actualSupport psi}

/-- Fix one coherent finite enumeration of the actual-support subtype. -/
noncomputable instance supportIndexFintype (psi : SS.State n ℂ) :
    Fintype (SupportIndex psi) :=
  Fintype.ofFinite (SupportIndex psi)

/-- A Boolean vertex of the cube, embedded coordinatewise in the reals. -/
def bitPoint (x : SS.BitString n) : Fin n → ℝ :=
  fun j => if x j then 1 else 0

/-- The positive probability attached to an actual-support point. -/
def supportProbability (psi : SS.State n ℂ) (x : SupportIndex psi) : ℝ :=
  Complex.normSq (psi x.1)

/-- The cube point attached to an actual-support index. -/
def supportPoint (psi : SS.State n ℂ) (x : SupportIndex psi) :
    Fin n → ℝ :=
  bitPoint x.1

/-- The subtype presentation neither drops an actual support point nor adds a
ghost point.  Its range is exactly the coordinatewise real embedding of the
paper's nonzero support. -/
theorem range_supportPoint (psi : SS.State n ℂ) :
    Set.range (supportPoint psi) = bitPoint '' actualSupport psi := by
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

/-- The probability-weighted mean of the actual support. -/
def stateMean (psi : SS.State n ℂ) : Fin n → ℝ :=
  fun j => ∑ x : SupportIndex psi,
    supportProbability psi x * supportPoint psi x j

/-- The covariance of the actual support about its own mean. -/
def stateCovariance (psi : SS.State n ℂ) : Matrix (Fin n) (Fin n) ℝ :=
  Covariance.cov (supportProbability psi) (supportPoint psi) (stateMean psi)

theorem supportProbability_pos (psi : SS.State n ℂ)
    (x : SupportIndex psi) :
    0 < supportProbability psi x := by
  exact Complex.normSq_pos.mpr x.2

theorem outside_actualSupportFinset (psi : SS.State n ℂ) :
    ∀ x, x ∉ actualSupportFinset psi → psi x = 0 := by
  classical
  intro x hx
  simpa [actualSupportFinset, actualSupport] using hx

theorem actualSupport_nonempty (psi : SS.State n ℂ)
    (hnorm : SS.innerC psi psi = 1) :
    (actualSupport psi).Nonempty := by
  by_contra h
  have hall : ∀ x, psi x = 0 := by
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have hzero : psi = 0 := funext hall
  rw [hzero] at hnorm
  simp [SS.innerC] at hnorm

theorem sum_supportProbability_eq_massOn (psi : SS.State n ℂ) :
    (∑ x : SupportIndex psi, supportProbability psi x) =
      SixQubit.massOn (actualSupportFinset psi) psi := by
  classical
  calc
    (∑ x : SupportIndex psi, supportProbability psi x) =
        ∑ x ∈ actualSupportFinset psi, Complex.normSq (psi x) := by
      exact (Finset.sum_subtype (actualSupportFinset psi)
        (by simp [actualSupportFinset, actualSupport])
        (fun x => Complex.normSq (psi x))).symm
    _ = SixQubit.massOn (actualSupportFinset psi) psi := rfl

theorem sum_supportProbability_eq_one (psi : SS.State n ℂ)
    (hnorm : SS.innerC psi psi = 1) :
    ∑ x : SupportIndex psi, supportProbability psi x = 1 := by
  rw [sum_supportProbability_eq_massOn]
  exact SixQubit.massOn_eq_one (actualSupportFinset psi) psi
    (outside_actualSupportFinset psi) hnorm

/-! ## Identifying the subtype sums with occupation numbers -/

theorem sum_probability_coordinate_eq_occOn (psi : SS.State n ℂ)
    (j : Fin n) :
    (∑ x : SupportIndex psi,
        supportProbability psi x * supportPoint psi x j) =
      SixQubit.occOn (actualSupportFinset psi) psi j := by
  classical
  calc
    (∑ x : SupportIndex psi,
        supportProbability psi x * supportPoint psi x j) =
        ∑ x ∈ actualSupportFinset psi,
          Complex.normSq (psi x) * bitPoint x j := by
      exact (Finset.sum_subtype (actualSupportFinset psi)
        (by simp [actualSupportFinset, actualSupport])
        (fun x => Complex.normSq (psi x) * bitPoint x j)).symm
    _ = SixQubit.occOn (actualSupportFinset psi) psi j := by
      rw [SixQubit.occOn, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      cases h : x j <;> simp [bitPoint, h]

theorem sum_probability_coordinate_mul_eq_occ2On (psi : SS.State n ℂ)
    (i j : Fin n) :
    (∑ x : SupportIndex psi,
        supportProbability psi x * supportPoint psi x i * supportPoint psi x j) =
      SixQubit.occ2On (actualSupportFinset psi) psi i j := by
  classical
  calc
    (∑ x : SupportIndex psi,
        supportProbability psi x * supportPoint psi x i * supportPoint psi x j) =
        ∑ x ∈ actualSupportFinset psi,
          Complex.normSq (psi x) * bitPoint x i * bitPoint x j := by
      exact (Finset.sum_subtype (actualSupportFinset psi)
        (by simp [actualSupportFinset, actualSupport])
        (fun x => Complex.normSq (psi x) * bitPoint x i * bitPoint x j)).symm
    _ = SixQubit.occ2On (actualSupportFinset psi) psi i j := by
      rw [SixQubit.occ2On, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      cases hi : x i <;> cases hj : x j <;> simp [bitPoint, hi, hj]

theorem stateMean_eq_occOn (psi : SS.State n ℂ) :
    stateMean psi = fun j => SixQubit.occOn (actualSupportFinset psi) psi j := by
  funext j
  exact sum_probability_coordinate_eq_occOn psi j

/-- The covariance defined from the actual-support subtype is exactly the
usual `second moment - mean × mean` expression used by the code-facing KL
lemmas. -/
theorem stateCovariance_eq_occ (psi : SS.State n ℂ)
    (hnorm : SS.innerC psi psi = 1) :
    stateCovariance psi = fun i j =>
      SixQubit.occ2On (actualSupportFinset psi) psi i j -
        SixQubit.occOn (actualSupportFinset psi) psi i *
          SixQubit.occOn (actualSupportFinset psi) psi j := by
  funext i j
  change (∑ x : SupportIndex psi,
      supportProbability psi x *
        (supportPoint psi x i - stateMean psi i) *
        (supportPoint psi x j - stateMean psi j)) = _
  calc
    (∑ x : SupportIndex psi,
      supportProbability psi x *
        (supportPoint psi x i - stateMean psi i) *
        (supportPoint psi x j - stateMean psi j)) =
      ∑ x : SupportIndex psi,
        (((supportProbability psi x * supportPoint psi x i * supportPoint psi x j -
            stateMean psi j *
              (supportProbability psi x * supportPoint psi x i)) -
            stateMean psi i *
              (supportProbability psi x * supportPoint psi x j)) +
          (stateMean psi i * stateMean psi j) * supportProbability psi x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = SixQubit.occ2On (actualSupportFinset psi) psi i j -
        SixQubit.occOn (actualSupportFinset psi) psi i *
          SixQubit.occOn (actualSupportFinset psi) psi j := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      rw [sum_probability_coordinate_mul_eq_occ2On,
        sum_probability_coordinate_eq_occOn,
        sum_probability_coordinate_eq_occOn,
        sum_supportProbability_eq_one psi hnorm, stateMean_eq_occOn]
      ring

/-! ## The code-to-geometry bridge -/

theorem commonMean_of_hasDistance
    (c d : SS.State n ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    stateMean c = stateMean d := by
  have hocc := MainTheory.AffineSpan.mean_eq_of_hasDistance
    (actualSupportFinset c) (actualSupportFinset d) c d
    (outside_actualSupportFinset c) (outside_actualSupportFinset d)
    hnc hnd hdist
  exact (stateMean_eq_occOn c).trans (hocc.trans (stateMean_eq_occOn d).symm)

theorem commonCovariance_of_hasDistance
    (c d : SS.State n ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    stateCovariance c = stateCovariance d := by
  rw [stateCovariance_eq_occ c hnc, stateCovariance_eq_occ d hnd]
  funext i j
  exact MainTheory.AffineSpan.covariance_eq_of_hasDistance
    (actualSupportFinset c) (actualSupportFinset d) c d
    (outside_actualSupportFinset c) (outside_actualSupportFinset d)
    hnc hnd hdist i j

theorem commonAffineSpan_of_hasDistance
    (c d : SS.State n ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    affineSpan ℝ (Set.range (supportPoint c)) =
      affineSpan ℝ (Set.range (supportPoint d)) := by
  have hmean := commonMean_of_hasDistance c d hnc hnd hdist
  have hcov := commonCovariance_of_hasDistance c d hnc hnd hdist
  have hcovCommon :
      Covariance.cov (supportProbability c) (supportPoint c) (stateMean c) =
        Covariance.cov (supportProbability d) (supportPoint d) (stateMean c) := by
    calc
      Covariance.cov (supportProbability c) (supportPoint c) (stateMean c) =
          stateCovariance c := rfl
      _ = stateCovariance d := hcov
      _ = Covariance.cov (supportProbability d) (supportPoint d) (stateMean d) := rfl
      _ = Covariance.cov (supportProbability d) (supportPoint d) (stateMean c) := by
        rw [hmean]
  exact Covariance.affineSpan_eq_of_cov_eq₂
    (supportProbability c) (supportProbability d)
    (supportPoint c) (supportPoint d) (stateMean c)
    (supportProbability_pos c) (supportProbability_pos d)
    (sum_supportProbability_eq_one c hnc)
    (sum_supportProbability_eq_one d hnd)
    rfl hmean.symm hcovCommon

/-- The preceding result written literally for the real embeddings of the two
actual nonzero support sets. -/
theorem commonAffineSpan_actualSupport_of_hasDistance
    (c d : SS.State n ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    affineSpan ℝ (bitPoint '' actualSupport c) =
      affineSpan ℝ (bitPoint '' actualSupport d) := by
  rw [← range_supportPoint, ← range_supportPoint]
  exact commonAffineSpan_of_hasDistance c d hnc hnd hdist

/-- All conclusions of the paper's common-affine-span lemma, expressed for
the actual nonzero supports of two normalized logical states. -/
structure CommonAffineSpanCertificate
    (c d : SS.State n ℂ) : Prop where
  support0_nonempty : (actualSupport c).Nonempty
  support1_nonempty : (actualSupport d).Nonempty
  probability0_pos : ∀ x : SupportIndex c, 0 < supportProbability c x
  probability1_pos : ∀ x : SupportIndex d, 0 < supportProbability d x
  probability0_sum : ∑ x : SupportIndex c, supportProbability c x = 1
  probability1_sum : ∑ x : SupportIndex d, supportProbability d x = 1
  mean_eq : stateMean c = stateMean d
  covariance_eq : stateCovariance c = stateCovariance d
  affineSpan_eq :
    affineSpan ℝ (bitPoint '' actualSupport c) =
      affineSpan ℝ (bitPoint '' actualSupport d)

theorem certificate_of_hasDistance
    (c d : SS.State n ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    CommonAffineSpanCertificate c d where
  support0_nonempty := actualSupport_nonempty c hnc
  support1_nonempty := actualSupport_nonempty d hnd
  probability0_pos := supportProbability_pos c
  probability1_pos := supportProbability_pos d
  probability0_sum := sum_supportProbability_eq_one c hnc
  probability1_sum := sum_supportProbability_eq_one d hnd
  mean_eq := commonMean_of_hasDistance c d hnc hnd hdist
  covariance_eq := commonCovariance_of_hasDistance c d hnc hnd hdist
  affineSpan_eq := commonAffineSpan_actualSupport_of_hasDistance c d hnc hnd hdist

private theorem exactCodeFrame_distance_three
    (C : CodeSpec.ExactCode n 2 d) (G : CodeSpec.OrthonormalFrame n 2)
    (hspan : CodeSpec.codeSpan C.frame = CodeSpec.codeSpan G)
    (hd : 3 ≤ d) :
    SS.HasDistance G.vec 3 := by
  have hdist : SS.HasDistance G.vec d :=
    CodeSpec.hasDistance_of_codeSpan_eq C.frame G hspan C.hasDistance
  intro P hP
  exact hdist P (by omega)

/-- The common-affine-span certificate applies to any orthonormal logical
frame spanning the exact code, not only to the distinguished frame stored in
`ExactCode`.  This is the form used for a supplied logical eigenbasis: the
eigenvalue/sector assertion selects `G`, while the proof below uses only its
orthonormality, equality of code spans, and the genuine KL distance property.
-/
theorem commonAffineSpan_of_exactCodeFrame
    (C : CodeSpec.ExactCode n 2 d) (G : CodeSpec.OrthonormalFrame n 2)
    (hspan : CodeSpec.codeSpan C.frame = CodeSpec.codeSpan G)
    (hd : 3 ≤ d) :
    CommonAffineSpanCertificate (G.vec 0) (G.vec 1) := by
  have hn0 : SS.innerC (G.vec 0) (G.vec 0) = 1 := by
    simpa using G.orthonormal 0 0
  have hn1 : SS.innerC (G.vec 1) (G.vec 1) = 1 := by
    simpa using G.orthonormal 1 1
  have hdist := exactCodeFrame_distance_three C G hspan hd
  have hvec : G.vec = ![G.vec 0, G.vec 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hvec] at hdist
  exact certificate_of_hasDistance (G.vec 0) (G.vec 1) hn0 hn1 hdist

/-- **Paper-facing end-to-end wrapper.**

An exact rank-two code of distance at least three has strictly positive
probability distributions on the actual supports of its two stored logical
frame vectors; those distributions have a common mean and covariance, and the
two actual supports have the same affine span.
-/
theorem commonAffineSpan_of_exactCode
    (C : CodeSpec.ExactCode n 2 d) (hd : 3 ≤ d) :
    CommonAffineSpanCertificate (C.frame.vec 0) (C.frame.vec 1) := by
  exact commonAffineSpan_of_exactCodeFrame C C.frame rfl hd

end

end MainTheory.CodeAffineSpanBridge
