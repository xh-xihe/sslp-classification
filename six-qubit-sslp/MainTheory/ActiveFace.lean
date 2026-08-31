import Mathlib
import MainTheory.Covariance

/-!
# The active face

The maximum-support-rank lemma of `main.tex` (Section 7) rests on one convexity
observation: if for every active variable there is a feasible point positive at
that variable, then averaging those finitely many points gives a *single*
feasible point positive at all of them at once.  Its support is therefore the
full active set, and no feasible point can have larger support.

That observation is what this file proves.  Nothing here is about codes or
moments -- it is a statement about a convex set of nonnegative vectors -- and
separating it out makes clear that the lemma's geometry is elementary and that
the work is entirely in identifying the active set, which the paper does with
exact linear-programming certificates outside Lean.
-/

namespace MainTheory.ActiveFace

variable {iota : Type*} [Fintype iota] [Nonempty iota]

/-- A coordinate is active when some feasible point is strictly positive
there.  This intrinsic definition does not depend on an LP representation. -/
def Active (K : Set (iota → ℝ)) : Set iota :=
  {j | ∃ p ∈ K, 0 < p j}

/-- The strict (positive) support of a nonnegative vector. -/
noncomputable def positiveSupport (p : iota → ℝ) : Finset iota :=
  Finset.univ.filter fun j => 0 < p j

/-- The uniform average of a finite family of points. -/
noncomputable def avg (pt : iota → iota → ℝ) : iota → ℝ :=
  fun j => (∑ k, pt k j) / (Fintype.card iota : ℝ)

/-- **The average is feasible.**  Convexity, with uniform weights. -/
theorem avg_mem (K : Set (iota → ℝ)) (hK : Convex ℝ K)
    (pt : iota → iota → ℝ) (hmem : ∀ k, pt k ∈ K) :
    avg pt ∈ K := by
  have hcard : (0 : ℝ) < (Fintype.card iota : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hw : ∑ _k : iota, ((Fintype.card iota : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have := hK.sum_mem (t := (Finset.univ : Finset iota))
    (fun k _ => le_of_lt (inv_pos.2 hcard)) hw (fun k _ => hmem k)
  have heq : (∑ k, ((Fintype.card iota : ℝ))⁻¹ • pt k) = avg pt := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, avg]
    rw [← Finset.mul_sum, div_eq_inv_mul]
  rwa [heq] at this

/-- **The average is positive wherever any one point is.**

This is the step the lemma needs: the averaged point is simultaneously positive
on every active variable, so its support is the whole active set. -/
theorem avg_pos (pt : iota → iota → ℝ)
    (hnn : ∀ k j, 0 ≤ pt k j) (j : iota) (k0 : iota) (hk0 : 0 < pt k0 j) :
    0 < avg pt j := by
  have hcard : (0 : ℝ) < (Fintype.card iota : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine div_pos ?_ hcard
  have hle : (0 : ℝ) < ∑ k, pt k j := by
    refine Finset.sum_pos' (fun k _ => hnn k j) ⟨k0, Finset.mem_univ k0, hk0⟩
  exact hle

omit [Nonempty iota] in
/-- Every feasible point is supported on the active set. -/
theorem positiveSupport_subset_active (K : Set (iota → ℝ))
    {p : iota → ℝ} (hp : p ∈ K) :
    ∀ j ∈ positiveSupport p, j ∈ Active K := by
  intro j hj
  have hj' : 0 < p j := by simpa [positiveSupport] using hj
  exact ⟨p, hp, hj'⟩

/-- **Full-active-support theorem.**

For a nonempty convex set of coordinatewise nonnegative vectors, one feasible
point is positive at every active coordinate simultaneously. -/
theorem exists_positive_iff_active (K : Set (iota → ℝ))
    (hK : Convex ℝ K) (hne : K.Nonempty)
    (hnn : ∀ p ∈ K, ∀ j, 0 ≤ p j) :
    ∃ p ∈ K, ∀ j, 0 < p j ↔ j ∈ Active K := by
  classical
  let p₀ : iota → ℝ := Classical.choose hne
  have hp₀ : p₀ ∈ K := Classical.choose_spec hne
  let pt : iota → iota → ℝ := fun j =>
    if hj : j ∈ Active K then Classical.choose hj else p₀
  have hpt_mem : ∀ j, pt j ∈ K := by
    intro j
    simp only [pt]
    split_ifs with hj
    · exact (Classical.choose_spec hj).1
    · exact hp₀
  have hpt_nonneg : ∀ j k, 0 ≤ pt j k := by
    intro j k
    exact hnn (pt j) (hpt_mem j) k
  have hpt_pos : ∀ j, j ∈ Active K → 0 < pt j j := by
    intro j hj
    simp only [pt, dif_pos hj]
    exact (Classical.choose_spec hj).2
  have havg : avg pt ∈ K := avg_mem K hK pt hpt_mem
  refine ⟨avg pt, havg, ?_⟩
  intro j
  constructor
  · intro hj
    exact ⟨avg pt, havg, hj⟩
  · intro hj
    exact avg_pos pt hpt_nonneg j j (hpt_pos j hj)

/-- The point supplied above has exactly the active set as its finite support. -/
theorem exists_support_eq_active (K : Set (iota → ℝ))
    (hK : Convex ℝ K) (hne : K.Nonempty)
    (hnn : ∀ p ∈ K, ∀ j, 0 ≤ p j) :
    ∃ p ∈ K, (↑(positiveSupport p) : Set iota) = Active K := by
  classical
  obtain ⟨p, hp, hpa⟩ := exists_positive_iff_active K hK hne hnn
  refine ⟨p, hp, ?_⟩
  ext j
  simpa [positiveSupport] using hpa j

/-- The active-set cardinality is therefore the attained maximum support
cardinality among feasible points. -/
theorem exists_maximum_support (K : Set (iota → ℝ))
    (hK : Convex ℝ K) (hne : K.Nonempty)
    (hnn : ∀ p ∈ K, ∀ j, 0 ≤ p j) :
    ∃ p ∈ K, ∀ q ∈ K, (positiveSupport q).card ≤ (positiveSupport p).card := by
  classical
  obtain ⟨p, hp, hpa⟩ := exists_positive_iff_active K hK hne hnn
  refine ⟨p, hp, ?_⟩
  intro q hq
  apply Finset.card_le_card
  intro j hj
  have hactive := positiveSupport_subset_active K hq j hj
  have hpj : 0 < p j := (hpa j).2 hactive
  simpa [positiveSupport] using hpj

/-! ## Two-colour active affine rank -/

section TwoColor

variable {n : ℕ} {ι₀ ι₁ : Type*}
variable [Fintype ι₀] [Fintype ι₁] [Nonempty ι₀] [Nonempty ι₁]

/-- Physical points used by the positive support of the left colour. -/
def supportPointsLeft (pt : ι₀ → Fin n → ℝ)
    (p : Sum ι₀ ι₁ → ℝ) : Set (Fin n → ℝ) :=
  pt '' {i | 0 < p (Sum.inl i)}

/-- Physical points used by the positive support of the right colour. -/
def supportPointsRight (pt : ι₁ → Fin n → ℝ)
    (p : Sum ι₀ ι₁ → ℝ) : Set (Fin n → ℝ) :=
  pt '' {i | 0 < p (Sum.inr i)}

/-- All left-colour points whose variables are active on the feasible face. -/
def activePointsLeft (K : Set (Sum ι₀ ι₁ → ℝ))
    (pt : ι₀ → Fin n → ℝ) : Set (Fin n → ℝ) :=
  pt '' {i | Sum.inl i ∈ Active K}

/-- All right-colour points whose variables are active on the feasible face. -/
def activePointsRight (K : Set (Sum ι₀ ι₁ → ℝ))
    (pt : ι₁ → Fin n → ℝ) : Set (Fin n → ℝ) :=
  pt '' {i | Sum.inr i ∈ Active K}

/-- Finite versions of the two active index sets.  They make the exact finite
sums below independent of a global `DecidablePred` instance for `Active`. -/
noncomputable def activeLeftFinset (K : Set (Sum ι₀ ι₁ → ℝ)) : Finset ι₀ :=
  by
    classical
    exact Finset.univ.filter fun i => Sum.inl i ∈ Active K

noncomputable def activeRightFinset (K : Set (Sum ι₀ ι₁ → ℝ)) : Finset ι₁ :=
  by
    classical
    exact Finset.univ.filter fun i => Sum.inr i ∈ Active K

omit [Fintype ι₁] [Nonempty ι₀] [Nonempty ι₁] in
@[simp] theorem mem_activeLeftFinset
    (K : Set (Sum ι₀ ι₁ → ℝ)) (i : ι₀) :
    i ∈ activeLeftFinset K ↔ Sum.inl i ∈ Active K := by
  classical
  simp [activeLeftFinset]

omit [Fintype ι₀] [Nonempty ι₀] [Nonempty ι₁] in
@[simp] theorem mem_activeRightFinset
    (K : Set (Sum ι₀ ι₁ → ℝ)) (i : ι₁) :
    i ∈ activeRightFinset K ↔ Sum.inr i ∈ Active K := by
  classical
  simp [activeRightFinset]

/-- Affine dimension of a point set, expressed as the finite dimension of the
direction of its affine hull. -/
noncomputable def affineRank (S : Set (Fin n → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ S).direction

noncomputable def activeAffineRankLeft (K : Set (Sum ι₀ ι₁ → ℝ))
    (pt : ι₀ → Fin n → ℝ) : ℕ :=
  affineRank (activePointsLeft K pt)

noncomputable def activeAffineRankRight (K : Set (Sum ι₀ ι₁ → ℝ))
    (pt : ι₁ → Fin n → ℝ) : ℕ :=
  affineRank (activePointsRight K pt)

omit [Nonempty ι₀] in
/-- The generic active-support average, specialized to the two colour blocks,
attains both complete active point sets simultaneously. -/
theorem exists_attains_both_active_sets
    (K : Set (Sum ι₀ ι₁ → ℝ)) (hK : Convex ℝ K) (hne : K.Nonempty)
    (hnn : ∀ p ∈ K, ∀ j, 0 ≤ p j)
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ) :
    ∃ p ∈ K,
      supportPointsLeft pt0 p = activePointsLeft K pt0 ∧
      supportPointsRight pt1 p = activePointsRight K pt1 := by
  obtain ⟨p, hp, hpa⟩ := exists_positive_iff_active K hK hne hnn
  refine ⟨p, hp, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (hpa (Sum.inl i)).1 hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (hpa (Sum.inl i)).2 hi, rfl⟩
  · ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (hpa (Sum.inr i)).1 hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (hpa (Sum.inr i)).2 hi, rfl⟩

omit [Fintype ι₀] [Fintype ι₁] [Nonempty ι₀] [Nonempty ι₁] in
/-- Every feasible support is contained in the corresponding active set. -/
theorem supportPointsLeft_subset_active
    (K : Set (Sum ι₀ ι₁ → ℝ)) (pt0 : ι₀ → Fin n → ℝ)
    {p : Sum ι₀ ι₁ → ℝ} (hp : p ∈ K) :
    supportPointsLeft pt0 p ⊆ activePointsLeft K pt0 := by
  rintro y ⟨i, hi, rfl⟩
  exact ⟨i, ⟨p, hp, hi⟩, rfl⟩

omit [Fintype ι₀] [Fintype ι₁] [Nonempty ι₀] [Nonempty ι₁] in
theorem supportPointsRight_subset_active
    (K : Set (Sum ι₀ ι₁ → ℝ)) (pt1 : ι₁ → Fin n → ℝ)
    {p : Sum ι₀ ι₁ → ℝ} (hp : p ∈ K) :
    supportPointsRight pt1 p ⊆ activePointsRight K pt1 := by
  rintro y ⟨i, hi, rfl⟩
  exact ⟨i, ⟨p, hp, hi⟩, rfl⟩

omit [Fintype ι₀] [Fintype ι₁] [Nonempty ι₀] [Nonempty ι₁] in
/-- No feasible distribution has larger left or right affine rank than the
active face. -/
theorem feasible_affineRank_le_active
    (K : Set (Sum ι₀ ι₁ → ℝ))
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ)
    {p : Sum ι₀ ι₁ → ℝ} (hp : p ∈ K) :
    affineRank (supportPointsLeft pt0 p) ≤ activeAffineRankLeft K pt0 ∧
    affineRank (supportPointsRight pt1 p) ≤ activeAffineRankRight K pt1 := by
  constructor
  · apply Submodule.finrank_mono
    apply AffineSubspace.direction_le
    exact affineSpan_mono ℝ (supportPointsLeft_subset_active K pt0 hp)
  · apply Submodule.finrank_mono
    apply AffineSubspace.direction_le
    exact affineSpan_mono ℝ (supportPointsRight_subset_active K pt1 hp)

/-- Moment data on the active variables.  Stating it as a structure prevents
the common mean, normalization, and covariance premises from being silently
mixed between unrelated feasible points. -/
structure ActiveMomentData (K : Set (Sum ι₀ ι₁ → ℝ))
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ) where
  mean : (Sum ι₀ ι₁ → ℝ) → Fin n → ℝ
  norm0 : ∀ p ∈ K,
    ∑ i : {i : ι₀ // i ∈ activeLeftFinset K}, p (Sum.inl i.1) = 1
  norm1 : ∀ p ∈ K,
    ∑ i : {i : ι₁ // i ∈ activeRightFinset K}, p (Sum.inr i.1) = 1
  mean0 : ∀ p ∈ K,
    (fun j => ∑ i : {i : ι₀ // i ∈ activeLeftFinset K},
      p (Sum.inl i.1) * pt0 i.1 j) = mean p
  mean1 : ∀ p ∈ K,
    (fun j => ∑ i : {i : ι₁ // i ∈ activeRightFinset K},
      p (Sum.inr i.1) * pt1 i.1 j) = mean p
  covariance : ∀ p ∈ K,
    Covariance.cov
        (fun i : {i : ι₀ // i ∈ activeLeftFinset K} => p (Sum.inl i.1))
        (fun i => pt0 i.1) (mean p) =
      Covariance.cov
        (fun i : {i : ι₁ // i ∈ activeRightFinset K} => p (Sum.inr i.1))
        (fun i => pt1 i.1) (mean p)

omit [Nonempty ι₀] in
/-- **The equality `affdim U₀ = affdim U₁` in Lemma 7.2.** -/
theorem active_affineSpan_eq
    (K : Set (Sum ι₀ ι₁ → ℝ)) (hK : Convex ℝ K) (hne : K.Nonempty)
    (hnn : ∀ p ∈ K, ∀ j, 0 ≤ p j)
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ)
    (M : ActiveMomentData K pt0 pt1) :
    affineSpan ℝ (activePointsLeft K pt0) =
      affineSpan ℝ (activePointsRight K pt1) := by
  obtain ⟨p, hp, hpa⟩ := exists_positive_iff_active K hK hne hnn
  let I0 := {i : ι₀ // i ∈ activeLeftFinset K}
  let I1 := {i : ι₁ // i ∈ activeRightFinset K}
  have hpos0 : ∀ i : I0, 0 < p (Sum.inl i.1) := by
    intro i
    apply (hpa (Sum.inl i.1)).2
    exact (mem_activeLeftFinset K i.1).1 i.2
  have hpos1 : ∀ i : I1, 0 < p (Sum.inr i.1) := by
    intro i
    apply (hpa (Sum.inr i.1)).2
    exact (mem_activeRightFinset K i.1).1 i.2
  have hspan := Covariance.affineSpan_eq_of_cov_eq₂
    (fun i : I0 => p (Sum.inl i.1))
    (fun i : I1 => p (Sum.inr i.1))
    (fun i : I0 => pt0 i.1) (fun i : I1 => pt1 i.1) (M.mean p)
    hpos0 hpos1 (M.norm0 p hp) (M.norm1 p hp)
    (M.mean0 p hp) (M.mean1 p hp) (M.covariance p hp)
  have hset0 : Set.range (fun i : I0 => pt0 i.1) =
      activePointsLeft K pt0 := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i.1, ?_, rfl⟩
      exact (mem_activeLeftFinset K i.1).1 i.2
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i, ?_⟩, rfl⟩
      exact (mem_activeLeftFinset K i).2 hi
  have hset1 : Set.range (fun i : I1 => pt1 i.1) =
      activePointsRight K pt1 := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i.1, ?_, rfl⟩
      exact (mem_activeRightFinset K i.1).1 i.2
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i, ?_⟩, rfl⟩
      exact (mem_activeRightFinset K i).2 hi
  simpa [hset0, hset1] using hspan

omit [Nonempty ι₀] in
theorem active_affineRank_eq
    (K : Set (Sum ι₀ ι₁ → ℝ)) (hK : Convex ℝ K) (hne : K.Nonempty)
    (hnn : ∀ p ∈ K, ∀ j, 0 ≤ p j)
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ)
    (M : ActiveMomentData K pt0 pt1) :
    activeAffineRankLeft K pt0 = activeAffineRankRight K pt1 := by
  unfold activeAffineRankLeft activeAffineRankRight affineRank
  rw [active_affineSpan_eq K hK hne hnn pt0 pt1 M]

omit [Nonempty ι₀] in
/-- **Maximum affine-rank and threshold criterion (Lemma 7.2).**

The active rank is attained, bounds every feasible support rank, and hence a
support of rank at least `rmin` exists exactly when `rmin ≤ r*`. -/
theorem rank_threshold_iff
    (K : Set (Sum ι₀ ι₁ → ℝ)) (hK : Convex ℝ K) (hne : K.Nonempty)
    (hnn : ∀ p ∈ K, ∀ j, 0 ≤ p j)
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ) (rmin : ℕ) :
    (∃ p ∈ K, rmin ≤ affineRank (supportPointsLeft pt0 p)) ↔
      rmin ≤ activeAffineRankLeft K pt0 := by
  constructor
  · rintro ⟨p, hp, hr⟩
    exact hr.trans (feasible_affineRank_le_active K pt0 pt1 hp).1
  · intro hr
    obtain ⟨p, hp, hleft, _⟩ :=
      exists_attains_both_active_sets K hK hne hnn pt0 pt1
    refine ⟨p, hp, ?_⟩
    simpa [activeAffineRankLeft, hleft] using hr

omit [Nonempty ι₀] in
/-- One headline packaging all three claims of the active-face lemma: equality
of the two active affine dimensions, maximality, and the threshold iff. -/
theorem maximum_support_rank_from_active_face
    (K : Set (Sum ι₀ ι₁ → ℝ)) (hK : Convex ℝ K) (hne : K.Nonempty)
    (hnn : ∀ p ∈ K, ∀ j, 0 ≤ p j)
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ)
    (M : ActiveMomentData K pt0 pt1) (rmin : ℕ) :
    activeAffineRankLeft K pt0 = activeAffineRankRight K pt1 ∧
      ((∃ p ∈ K, rmin ≤ affineRank (supportPointsLeft pt0 p)) ↔
        rmin ≤ activeAffineRankLeft K pt0) := by
  exact ⟨active_affineRank_eq K hK hne hnn pt0 pt1 M,
    rank_threshold_iff K hK hne hnn pt0 pt1 rmin⟩

end TwoColor

end MainTheory.ActiveFace
