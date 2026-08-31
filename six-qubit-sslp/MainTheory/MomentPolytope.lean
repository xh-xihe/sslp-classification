import Mathlib
import MainTheory.ActiveFace

/-!
# The concrete six-bit degree-two moment polytope

Section 7 of `documents/20260822/main.tex` uses one exact polytope for each
pair of coloured Boolean fibres.  A point of the polytope consists of two
nonnegative probability vectors.  Each colour has total mass one, their six
first moments agree, and their fifteen square-free second moments agree.

This file gives that object a paper-facing Lean definition.  It then derives,
rather than assumes, the common mean and covariance needed by
`ActiveFace.ActiveMomentData`.  Consequently the generic active-face theorem
really applies to this degree-two moment polytope and yields the concrete
maximum-support-rank and threshold statements used by the enumeration.
-/

namespace MainTheory.MomentPolytope

open MainTheory

noncomputable section

/-! ## Six Boolean coordinates and the fifteen unordered pairs -/

/-- A Boolean point in the six-cube. -/
abbrev BitPoint6 := Fin 6 → Bool

/-- A Boolean coordinate viewed as a real number. -/
def coord (x : BitPoint6) (j : Fin 6) : ℝ :=
  if x j then 1 else 0

@[simp] theorem coord_mul_self (x : BitPoint6) (j : Fin 6) :
    coord x j * coord x j = coord x j := by
  cases h : x j <;> simp [coord, h]

/-- The square-free degree-two coordinates, indexed without repetition. -/
abbrev Pair6 := {jk : Fin 6 × Fin 6 // jk.1 < jk.2}

/-- There are exactly six first-moment and fifteen second-moment rows. -/
theorem moment_row_counts :
    Fintype.card (Fin 6) = 6 ∧ Fintype.card Pair6 = 15 := by
  decide

/-! ## The two-colour feasible set -/

variable {I₀ I₁ : Type*} [Fintype I₀] [Fintype I₁]

/-- Left-colour first moment. -/
def mean0 (x₀ : I₀ → BitPoint6) (p : Sum I₀ I₁ → ℝ) : Fin 6 → ℝ :=
  fun j => ∑ i : I₀, p (Sum.inl i) * coord (x₀ i) j

/-- Right-colour first moment. -/
def mean1 (x₁ : I₁ → BitPoint6) (p : Sum I₀ I₁ → ℝ) : Fin 6 → ℝ :=
  fun j => ∑ i : I₁, p (Sum.inr i) * coord (x₁ i) j

/-- Left-colour raw second moment. -/
def second0 (x₀ : I₀ → BitPoint6) (p : Sum I₀ I₁ → ℝ)
    (j k : Fin 6) : ℝ :=
  ∑ i : I₀, p (Sum.inl i) * coord (x₀ i) j * coord (x₀ i) k

/-- Right-colour raw second moment. -/
def second1 (x₁ : I₁ → BitPoint6) (p : Sum I₀ I₁ → ℝ)
    (j k : Fin 6) : ℝ :=
  ∑ i : I₁, p (Sum.inr i) * coord (x₁ i) j * coord (x₁ i) k

/-- The exact constraints defining the two-colour degree-`<= 2` moment
polytope: nonnegativity, two normalizations, six first-moment equations, and
fifteen square-free second-moment equations. -/
structure Feasible (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6)
    (p : Sum I₀ I₁ → ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ p z
  norm0 : ∑ i : I₀, p (Sum.inl i) = 1
  norm1 : ∑ i : I₁, p (Sum.inr i) = 1
  firstMoment : ∀ j : Fin 6, mean0 x₀ p j = mean1 x₁ p j
  secondMoment : ∀ jk : Pair6,
    second0 x₀ p jk.1.1 jk.1.2 = second1 x₁ p jk.1.1 jk.1.2

/-- The concrete moment polytope as a set of the two concatenated colour
blocks. -/
def momentPolytope (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6) :
    Set (Sum I₀ I₁ → ℝ) :=
  {p | Feasible x₀ x₁ p}

private theorem sum_mix_mul {I : Type*} [Fintype I]
    (a b : ℝ) (p q f : I → ℝ) :
    (∑ i, (a * p i + b * q i) * f i) =
      a * (∑ i, p i * f i) + b * (∑ i, q i * f i) := by
  calc
    _ = ∑ i, (a * (p i * f i) + b * (q i * f i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- The degree-two moment feasible set is convex. -/
theorem momentPolytope_convex (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6) :
    Convex ℝ (momentPolytope x₀ x₁) := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨hpnn, hp0, hp1, hpfirst, hpsecond⟩
  rcases hq with ⟨hqnn, hq0, hq1, hqfirst, hqsecond⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hpnn z)) (mul_nonneg hb (hqnn z))
  · have h := sum_mix_mul a b
        (fun i : I₀ => p (Sum.inl i)) (fun i => q (Sum.inl i)) (fun _ => (1 : ℝ))
    simpa [hp0, hq0, hab] using h
  · have h := sum_mix_mul a b
        (fun i : I₁ => p (Sum.inr i)) (fun i => q (Sum.inr i)) (fun _ => (1 : ℝ))
    simpa [hp1, hq1, hab] using h
  · intro j
    change (∑ i : I₀, (a * p (Sum.inl i) + b * q (Sum.inl i)) * coord (x₀ i) j) =
      ∑ i : I₁, (a * p (Sum.inr i) + b * q (Sum.inr i)) * coord (x₁ i) j
    rw [sum_mix_mul, sum_mix_mul]
    have hpj : (∑ i : I₀, p (Sum.inl i) * coord (x₀ i) j) =
        ∑ i : I₁, p (Sum.inr i) * coord (x₁ i) j := by
      simpa [mean0, mean1] using hpfirst j
    have hqj : (∑ i : I₀, q (Sum.inl i) * coord (x₀ i) j) =
        ∑ i : I₁, q (Sum.inr i) * coord (x₁ i) j := by
      simpa [mean0, mean1] using hqfirst j
    rw [hpj, hqj]
  · intro jk
    have hleft := sum_mix_mul a b
      (fun i : I₀ => p (Sum.inl i)) (fun i => q (Sum.inl i))
      (fun i => coord (x₀ i) jk.1.1 * coord (x₀ i) jk.1.2)
    have hright := sum_mix_mul a b
      (fun i : I₁ => p (Sum.inr i)) (fun i => q (Sum.inr i))
      (fun i => coord (x₁ i) jk.1.1 * coord (x₁ i) jk.1.2)
    calc
      second0 x₀ (a • p + b • q) jk.1.1 jk.1.2 =
          a * second0 x₀ p jk.1.1 jk.1.2 + b * second0 x₀ q jk.1.1 jk.1.2 := by
        simpa [second0, mul_assoc] using hleft
      _ = a * second1 x₁ p jk.1.1 jk.1.2 + b * second1 x₁ q jk.1.1 jk.1.2 := by
        rw [hpsecond jk, hqsecond jk]
      _ = second1 x₁ (a • p + b • q) jk.1.1 jk.1.2 := by
        simpa [second1, mul_assoc] using hright.symm

/-- Feasibility supplies the coordinatewise nonnegativity expected by the
generic active-face API. -/
theorem momentPolytope_nonneg (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6) :
    ∀ p ∈ momentPolytope x₀ x₁, ∀ z, 0 ≤ p z := by
  intro p hp z
  exact hp.nonneg z

/-! ## All raw second moments and the covariance -/

/-- The six first moments determine the repeated-index second moments because
the physical coordinates are Boolean; together with the fifteen declared
rows, this gives equality for every ordered coordinate pair. -/
theorem secondMoment_eq (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6)
    {p : Sum I₀ I₁ → ℝ} (hp : p ∈ momentPolytope x₀ x₁)
    (j k : Fin 6) :
    second0 x₀ p j k = second1 x₁ p j k := by
  rcases lt_trichotomy j k with hjk | hjk | hjk
  · exact hp.secondMoment ⟨(j, k), hjk⟩
  · subst k
    calc
      second0 x₀ p j j = mean0 x₀ p j := by
        unfold second0 mean0
        apply Finset.sum_congr rfl
        intro i _
        calc
          p (Sum.inl i) * coord (x₀ i) j * coord (x₀ i) j =
              p (Sum.inl i) * (coord (x₀ i) j * coord (x₀ i) j) := by ring
          _ = p (Sum.inl i) * coord (x₀ i) j := by rw [coord_mul_self]
      _ = mean1 x₁ p j := hp.firstMoment j
      _ = second1 x₁ p j j := by
        unfold second1 mean1
        symm
        apply Finset.sum_congr rfl
        intro i _
        calc
          p (Sum.inr i) * coord (x₁ i) j * coord (x₁ i) j =
              p (Sum.inr i) * (coord (x₁ i) j * coord (x₁ i) j) := by ring
          _ = p (Sum.inr i) * coord (x₁ i) j := by rw [coord_mul_self]
  · have h := hp.secondMoment ⟨(k, j), hjk⟩
    calc
      second0 x₀ p j k = second0 x₀ p k j := by
        unfold second0
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = second1 x₁ p k j := h
      _ = second1 x₁ p j k := by
        unfold second1
        apply Finset.sum_congr rfl
        intro i _
        ring

private theorem cov_eq_second_sub {I : Type*} [Fintype I]
    (p : I → ℝ) (pt : I → Fin 6 → ℝ) (mu : Fin 6 → ℝ)
    (hnorm : ∑ i, p i = 1)
    (hmean : (fun j => ∑ i, p i * pt i j) = mu)
    (j k : Fin 6) :
    Covariance.cov p pt mu j k =
      (∑ i, p i * pt i j * pt i k) - mu j * mu k := by
  rw [Covariance.cov]
  calc
    (∑ i, p i * (pt i j - mu j) * (pt i k - mu k)) =
        ∑ i, (p i * pt i j * pt i k - (p i * pt i j) * mu k -
          mu j * (p i * pt i k) + (mu j * mu k) * p i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (∑ i, p i * pt i j * pt i k) - mu j * mu k := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      have hj : (∑ i, p i * pt i j * mu k) = mu j * mu k := by
        rw [← Finset.sum_mul, congrFun hmean j]
      have hk : (∑ i, mu j * (p i * pt i k)) = mu j * mu k := by
        rw [← Finset.mul_sum, congrFun hmean k]
      have hn : (∑ i, (mu j * mu k) * p i) = mu j * mu k := by
        rw [← Finset.mul_sum, hnorm, mul_one]
      rw [hj, hk, hn]
      ring

/-- The declared degree-two equations imply equality of the two covariance
matrices about their common first moment. -/
theorem covariance_eq (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6)
    {p : Sum I₀ I₁ → ℝ} (hp : p ∈ momentPolytope x₀ x₁) :
    Covariance.cov (fun i : I₀ => p (Sum.inl i)) (fun i => coord (x₀ i)) (mean0 x₀ p) =
      Covariance.cov (fun i : I₁ => p (Sum.inr i)) (fun i => coord (x₁ i)) (mean0 x₀ p) := by
  have hm0 : (fun j => ∑ i : I₀, p (Sum.inl i) * coord (x₀ i) j) = mean0 x₀ p := rfl
  have hm1 : (fun j => ∑ i : I₁, p (Sum.inr i) * coord (x₁ i) j) = mean0 x₀ p := by
    funext j
    exact (hp.firstMoment j).symm
  ext j k
  rw [cov_eq_second_sub _ _ _ hp.norm0 hm0 j k,
    cov_eq_second_sub _ _ _ hp.norm1 hm1 j k]
  exact congrArg (fun z => z - mean0 x₀ p j * mean0 x₀ p k)
    (secondMoment_eq x₀ x₁ hp j k)

/-! ## Restriction to the active variables -/

variable [Nonempty I₀] [Nonempty I₁]

omit [Nonempty I₀] [Nonempty I₁] in
private theorem eq_zero_of_not_active
    (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6)
    {p : Sum I₀ I₁ → ℝ} (hp : p ∈ momentPolytope x₀ x₁)
    {z : Sum I₀ I₁}
    (hz : z ∉ ActiveFace.Active (momentPolytope x₀ x₁)) : p z = 0 := by
  apply le_antisymm
  · exact le_of_not_gt fun hpos => hz ⟨p, hp, hpos⟩
  · exact hp.nonneg z

omit [Nonempty I₀] [Nonempty I₁] in
private theorem weighted_sum_activeLeft_eq
    (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6)
    {p : Sum I₀ I₁ → ℝ} (hp : p ∈ momentPolytope x₀ x₁)
    (g : I₀ → ℝ) :
    (∑ i : {i : I₀ // i ∈ ActiveFace.activeLeftFinset (momentPolytope x₀ x₁)},
      p (Sum.inl i.1) * g i.1) = ∑ i : I₀, p (Sum.inl i) * g i := by
  classical
  let s := ActiveFace.activeLeftFinset (momentPolytope x₀ x₁)
  calc
    _ = ∑ i ∈ s, p (Sum.inl i) * g i := by
      change (∑ i ∈ s.attach, p (Sum.inl i.1) * g i.1) = _
      simpa using Finset.sum_attach s (fun i => p (Sum.inl i) * g i)
    _ = ∑ i : I₀, p (Sum.inl i) * g i := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      have hnot : Sum.inl i ∉ ActiveFace.Active (momentPolytope x₀ x₁) := by
        intro hactive
        exact hi ((ActiveFace.mem_activeLeftFinset (momentPolytope x₀ x₁) i).2 hactive)
      rw [eq_zero_of_not_active x₀ x₁ hp hnot]
      simp

omit [Nonempty I₀] [Nonempty I₁] in
private theorem weighted_sum_activeRight_eq
    (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6)
    {p : Sum I₀ I₁ → ℝ} (hp : p ∈ momentPolytope x₀ x₁)
    (g : I₁ → ℝ) :
    (∑ i : {i : I₁ // i ∈ ActiveFace.activeRightFinset (momentPolytope x₀ x₁)},
      p (Sum.inr i.1) * g i.1) = ∑ i : I₁, p (Sum.inr i) * g i := by
  classical
  let s := ActiveFace.activeRightFinset (momentPolytope x₀ x₁)
  calc
    _ = ∑ i ∈ s, p (Sum.inr i) * g i := by
      change (∑ i ∈ s.attach, p (Sum.inr i.1) * g i.1) = _
      simpa using Finset.sum_attach s (fun i => p (Sum.inr i) * g i)
    _ = ∑ i : I₁, p (Sum.inr i) * g i := by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i _ hi
      have hnot : Sum.inr i ∉ ActiveFace.Active (momentPolytope x₀ x₁) := by
        intro hactive
        exact hi ((ActiveFace.mem_activeRightFinset (momentPolytope x₀ x₁) i).2 hactive)
      rw [eq_zero_of_not_active x₀ x₁ hp hnot]
      simp

/-- The concrete degree-two constraints provide every field of
`ActiveFace.ActiveMomentData`; in particular, common covariance is a theorem
above and is not an extra hypothesis of this constructor. -/
def activeMomentData (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6) :
    ActiveFace.ActiveMomentData (momentPolytope x₀ x₁)
      (fun i => coord (x₀ i)) (fun i => coord (x₁ i)) where
  mean := fun p => mean0 x₀ p
  norm0 := by
    intro p hp
    have h := weighted_sum_activeLeft_eq x₀ x₁ hp (fun _ => (1 : ℝ))
    have hfull : (∑ i : I₀, p (Sum.inl i) * 1) = 1 := by
      simpa using hp.norm0
    simpa using h.trans hfull
  norm1 := by
    intro p hp
    have h := weighted_sum_activeRight_eq x₀ x₁ hp (fun _ => (1 : ℝ))
    have hfull : (∑ i : I₁, p (Sum.inr i) * 1) = 1 := by
      simpa using hp.norm1
    simpa using h.trans hfull
  mean0 := by
    intro p hp
    funext j
    exact weighted_sum_activeLeft_eq x₀ x₁ hp (fun i => coord (x₀ i) j)
  mean1 := by
    intro p hp
    funext j
    calc
      _ = mean1 x₁ p j := weighted_sum_activeRight_eq x₀ x₁ hp
        (fun i => coord (x₁ i) j)
      _ = mean0 x₀ p j := (hp.firstMoment j).symm
  covariance := by
    intro p hp
    ext j k
    rw [Covariance.cov, Covariance.cov]
    have hleft := weighted_sum_activeLeft_eq x₀ x₁ hp
      (fun i => (coord (x₀ i) j - mean0 x₀ p j) *
        (coord (x₀ i) k - mean0 x₀ p k))
    have hright := weighted_sum_activeRight_eq x₀ x₁ hp
      (fun i => (coord (x₁ i) j - mean0 x₀ p j) *
        (coord (x₁ i) k - mean0 x₀ p k))
    calc
      _ = Covariance.cov (fun i : I₀ => p (Sum.inl i))
          (fun i => coord (x₀ i)) (mean0 x₀ p) j k := by
        simpa [Covariance.cov, mul_assoc] using hleft
      _ = Covariance.cov (fun i : I₁ => p (Sum.inr i))
          (fun i => coord (x₁ i)) (mean0 x₀ p) j k :=
        congrFun₂ (covariance_eq x₀ x₁ hp) j k
      _ = _ := by
        simpa [Covariance.cov, mul_assoc] using hright.symm

/-! ## Concrete maximum-support-rank headlines -/

omit [Nonempty I₀] in
/-- The maximum active affine rank is common to both colours and is attained
by one feasible moment point. -/
theorem exists_maximum_support_rank
    (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6)
    (hne : (momentPolytope x₀ x₁).Nonempty) :
    ActiveFace.activeAffineRankLeft (momentPolytope x₀ x₁) (fun i => coord (x₀ i)) =
        ActiveFace.activeAffineRankRight (momentPolytope x₀ x₁) (fun i => coord (x₁ i)) ∧
      ∃ p ∈ momentPolytope x₀ x₁,
        ActiveFace.supportPointsLeft (fun i => coord (x₀ i)) p =
          ActiveFace.activePointsLeft (momentPolytope x₀ x₁) (fun i => coord (x₀ i)) ∧
        ActiveFace.supportPointsRight (fun i => coord (x₁ i)) p =
          ActiveFace.activePointsRight (momentPolytope x₀ x₁) (fun i => coord (x₁ i)) := by
  constructor
  · exact ActiveFace.active_affineRank_eq _ (momentPolytope_convex x₀ x₁) hne
      (momentPolytope_nonneg x₀ x₁) _ _ (activeMomentData x₀ x₁)
  · exact ActiveFace.exists_attains_both_active_sets _ (momentPolytope_convex x₀ x₁)
      hne (momentPolytope_nonneg x₀ x₁) _ _

omit [Nonempty I₀] in
/-- **Concrete Lemma 7.2 threshold statement.**  For the six-bit degree-two
moment polytope, a feasible left support of affine rank at least `rmin` exists
iff `rmin` does not exceed the affine rank of the active face. -/
theorem rank_threshold_iff
    (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6)
    (hne : (momentPolytope x₀ x₁).Nonempty) (rmin : ℕ) :
    (∃ p ∈ momentPolytope x₀ x₁,
        rmin ≤ ActiveFace.affineRank
          (ActiveFace.supportPointsLeft (fun i => coord (x₀ i)) p)) ↔
      rmin ≤ ActiveFace.activeAffineRankLeft
        (momentPolytope x₀ x₁) (fun i => coord (x₀ i)) := by
  exact ActiveFace.rank_threshold_iff _ (momentPolytope_convex x₀ x₁) hne
    (momentPolytope_nonneg x₀ x₁) (fun i => coord (x₀ i))
    (fun i => coord (x₁ i)) rmin

omit [Nonempty I₀] in
/-- One paper-facing theorem packaging equality of the two active ranks and
the exact threshold criterion. -/
theorem maximum_support_rank_and_threshold
    (x₀ : I₀ → BitPoint6) (x₁ : I₁ → BitPoint6)
    (hne : (momentPolytope x₀ x₁).Nonempty) (rmin : ℕ) :
    ActiveFace.activeAffineRankLeft (momentPolytope x₀ x₁) (fun i => coord (x₀ i)) =
        ActiveFace.activeAffineRankRight (momentPolytope x₀ x₁) (fun i => coord (x₁ i)) ∧
      ((∃ p ∈ momentPolytope x₀ x₁,
          rmin ≤ ActiveFace.affineRank
            (ActiveFace.supportPointsLeft (fun i => coord (x₀ i)) p)) ↔
        rmin ≤ ActiveFace.activeAffineRankLeft
          (momentPolytope x₀ x₁) (fun i => coord (x₀ i))) := by
  exact ActiveFace.maximum_support_rank_from_active_face _
    (momentPolytope_convex x₀ x₁) hne (momentPolytope_nonneg x₀ x₁)
    _ _ (activeMomentData x₀ x₁) rmin

end

end MainTheory.MomentPolytope
