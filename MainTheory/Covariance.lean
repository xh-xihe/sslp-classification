import Mathlib

/-!
# The covariance quadratic form

Lemma 5.2 of `main.tex` (the common affine-span lemma) concludes that the two
logical supports have the same affine span.  Its proof has two halves.  The
first is quantum: the weight-one and weight-two diagonal Knill-Laflamme
equations make the first and second moments of the two supports agree, hence the
covariance matrices agree.  The second half is not quantum at all -- it is the
observation that for strictly positive weights,

    w^T Sigma w = 0   iff   w is orthogonal to every support point minus the mean,

so the range of `Sigma` is the span of the centred support, and the affine span
is recovered as `mu + range Sigma`.

This file is that second half, stated for an arbitrary finite weighted point
set.  Nothing here mentions codes, Paulis or distance; the quantum input enters
only as the hypothesis that the two covariance matrices coincide, which is where
`SixQubit/CodeBridge.lean` already supplies `occOn_eq_of_hasDistance` and
`occ2On_eq_of_hasDistance`.

Separating the two halves is the point: the geometric half is general, reusable,
and elementary, and keeping it apart from the moment computation makes clear
exactly how much of the lemma is about quantum codes at all.
-/

namespace MainTheory.Covariance

variable {n : ℕ} {iota : Type*} [Fintype iota]

/-! ## The covariance matrix and its quadratic form -/

/-- The covariance matrix of a weighted point set about a point `mu`. -/
def cov (p : iota → ℝ) (pt : iota → Fin n → ℝ) (mu : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ k, p k * (pt k i - mu i) * (pt k j - mu j)

/-- The centred coordinate of a point along a direction. -/
def proj (pt : iota → Fin n → ℝ) (mu w : Fin n → ℝ) (k : iota) : ℝ :=
  ∑ i, w i * (pt k i - mu i)

/-- **The quadratic form is a weighted sum of squares.**

`main.tex` eq. 5.24.  This is what makes the positivity argument work. -/
theorem quad_eq_sum_sq (p : iota → ℝ) (pt : iota → Fin n → ℝ)
    (mu w : Fin n → ℝ) :
    (∑ i, ∑ j, w i * cov p pt mu i j * w j)
      = ∑ k, p k * (proj pt mu w k) ^ 2 := by
  have hL : (∑ i, ∑ j, w i * cov p pt mu i j * w j)
      = ∑ i, ∑ j, ∑ k,
          w i * (p k * (pt k i - mu i) * (pt k j - mu j)) * w j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [cov, Finset.mul_sum, Finset.sum_mul]
  have hR : (∑ k, p k * (proj pt mu w k) ^ 2)
      = ∑ k, ∑ i, ∑ j,
          w i * (p k * (pt k i - mu i) * (pt k j - mu j)) * w j := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [proj, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL, hR]
  have inner : ∀ i : Fin n, (∑ j : Fin n, ∑ k : iota,
        w i * (p k * (pt k i - mu i) * (pt k j - mu j)) * w j)
      = ∑ k : iota, ∑ j : Fin n,
        w i * (p k * (pt k i - mu i) * (pt k j - mu j)) * w j :=
    fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => inner i)]
  exact Finset.sum_comm

/-! ## Positivity pins the kernel -/

/-- **With strictly positive weights, the quadratic form vanishes only on
directions orthogonal to the whole centred support.**

This is the step that identifies `range Sigma` with the span of the centred
support, and hence `aff(T)` with `mu + range Sigma`. -/
theorem quad_eq_zero_iff (p : iota → ℝ) (pt : iota → Fin n → ℝ)
    (mu w : Fin n → ℝ) (hp : ∀ k, 0 < p k) :
    (∑ i, ∑ j, w i * cov p pt mu i j * w j) = 0
      ↔ ∀ k, proj pt mu w k = 0 := by
  rw [quad_eq_sum_sq]
  constructor
  · intro h k
    have hnn : ∀ l ∈ Finset.univ, 0 ≤ p l * (proj pt mu w l) ^ 2 :=
      fun l _ => mul_nonneg (hp l).le (sq_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h k (Finset.mem_univ k)
    have := mul_eq_zero.1 hz
    rcases this with h1 | h1
    · exact absurd h1 (hp k).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1
  · intro h
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [h k]
    ring

/-- The quadratic form is nonnegative, which is the other half of `Sigma`
being positive semidefinite. -/
theorem quad_nonneg (p : iota → ℝ) (pt : iota → Fin n → ℝ)
    (mu w : Fin n → ℝ) (hp : ∀ k, 0 ≤ p k) :
    0 ≤ ∑ i, ∑ j, w i * cov p pt mu i j * w j := by
  rw [quad_eq_sum_sq]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hp k) (sq_nonneg _)

/-! ## Equal covariances give equal centred spans

The quantum input of Lemma 5.2 is exactly that the two covariance matrices
agree.  Given that, the two supports have the same set of orthogonal directions,
hence the same centred span and the same affine span. -/

/-- **Equal covariance forces equal orthogonal complements.**

With `Sigma_0 = Sigma_1` and both weight families strictly positive, a direction
kills one centred support exactly when it kills the other. -/
theorem proj_eq_zero_congr
    (p0 p1 : iota → ℝ) (pt0 pt1 : iota → Fin n → ℝ)
    (mu : Fin n → ℝ)
    (hp0 : ∀ k, 0 < p0 k) (hp1 : ∀ k, 0 < p1 k)
    (hcov : cov p0 pt0 mu = cov p1 pt1 mu) (w : Fin n → ℝ) :
    (∀ k, proj pt0 mu w k = 0) ↔ ∀ k, proj pt1 mu w k = 0 := by
  rw [← quad_eq_zero_iff p0 pt0 mu w hp0, ← quad_eq_zero_iff p1 pt1 mu w hp1,
    hcov]

/-! ## The centred spans coincide

`proj_eq_zero_congr` says a direction annihilates one centred support exactly
when it annihilates the other.  Since a subspace of a vector space is determined
by the functionals vanishing on it, that upgrades to equality of the two centred
spans -- the subspace `V` of `main.tex` eq. `eq:V-r`, and with it
`aff(T_0) = mu + V = aff(T_1)`.

An earlier draft of this development left this step open, calling it
bookkeeping.  It is short, but it is the step that turns the covariance
computation into the statement the lemma actually makes. -/

/-- Membership in the annihilator of a span is membership on the generators. -/
theorem mem_dualAnnihilator_span {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : Set V) (phi : Module.Dual ℝ V) :
    phi ∈ (Submodule.span ℝ S).dualAnnihilator ↔ ∀ x ∈ S, phi x = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h x hx
    exact h x (Submodule.subset_span hx)
  · intro h w hw
    have : Submodule.span ℝ S ≤ LinearMap.ker phi :=
      Submodule.span_le.2 (fun x hx => h x hx)
    exact this hw

/-- **The two centred supports span the same subspace.**

This is `eq:affine-V` of `main.tex`, in the linear form; the affine statement is
this together with `mu` lying in both affine spans, which holds because `mu` is a
convex combination of each support. -/
theorem span_eq_of_cov_eq
    (p0 p1 : iota → ℝ) (pt0 pt1 : iota → Fin n → ℝ)
    (mu : Fin n → ℝ)
    (hp0 : ∀ k, 0 < p0 k) (hp1 : ∀ k, 0 < p1 k)
    (hcov : cov p0 pt0 mu = cov p1 pt1 mu) :
    Submodule.span ℝ (Set.range fun k => pt0 k - mu)
      = Submodule.span ℝ (Set.range fun k => pt1 k - mu) := by
  rw [← Subspace.dualAnnihilator_inj]
  ext phi
  set e : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0 with he
  have hexp : ∀ v : Fin n → ℝ, phi v = ∑ i, v i * phi (e i) := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ phi v]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]
  have hproj : ∀ (pt : iota → Fin n → ℝ) (k : iota),
      phi (pt k - mu) = proj pt mu (fun i => phi (e i)) k := by
    intro pt k
    rw [hexp, proj]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply]; ring
  have key : ∀ pt : iota → Fin n → ℝ,
      (phi ∈ (Submodule.span ℝ (Set.range fun k => pt k - mu)).dualAnnihilator)
        ↔ ∀ k, proj pt mu (fun i => phi (e i)) k = 0 := by
    intro pt
    rw [mem_dualAnnihilator_span]
    constructor
    · intro h k
      rw [← hproj pt k]
      exact h _ (Set.mem_range_self k)
    · rintro h x ⟨k, rfl⟩
      rw [hproj pt k]
      exact h k
  rw [key pt0, key pt1]
  exact proj_eq_zero_congr p0 p1 pt0 pt1 mu hp0 hp1 hcov _

/-! The paper's two supports need not have the same cardinality.  The following
two theorems remove the artificial shared-index restriction of the original
interfaces above. -/

/-- Equal covariance identifies the annihilating directions even when the two
finite supports have different index types (and hence different sizes). -/
theorem proj_eq_zero_congr₂
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (p0 : ι₀ → ℝ) (p1 : ι₁ → ℝ)
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ)
    (mu : Fin n → ℝ)
    (hp0 : ∀ k, 0 < p0 k) (hp1 : ∀ k, 0 < p1 k)
    (hcov : cov p0 pt0 mu = cov p1 pt1 mu) (w : Fin n → ℝ) :
    (∀ k, proj pt0 mu w k = 0) ↔ ∀ k, proj pt1 mu w k = 0 := by
  rw [← quad_eq_zero_iff p0 pt0 mu w hp0,
    ← quad_eq_zero_iff p1 pt1 mu w hp1, hcov]

/-- **Common centred span for differently sized supports.**

This is the actual geometric form needed both by Lemma 5.2 and by the active
face Lemma 7.2. -/
theorem span_eq_of_cov_eq₂
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (p0 : ι₀ → ℝ) (p1 : ι₁ → ℝ)
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ)
    (mu : Fin n → ℝ)
    (hp0 : ∀ k, 0 < p0 k) (hp1 : ∀ k, 0 < p1 k)
    (hcov : cov p0 pt0 mu = cov p1 pt1 mu) :
    Submodule.span ℝ (Set.range fun k => pt0 k - mu) =
      Submodule.span ℝ (Set.range fun k => pt1 k - mu) := by
  rw [← Subspace.dualAnnihilator_inj]
  ext phi
  let e : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0
  have hexp : ∀ v : Fin n → ℝ, phi v = ∑ i, v i * phi (e i) := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ phi v]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]
  have hproj0 : ∀ k : ι₀,
      phi (pt0 k - mu) = proj pt0 mu (fun i => phi (e i)) k := by
    intro k
    rw [hexp, proj]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply]; ring
  have hproj1 : ∀ k : ι₁,
      phi (pt1 k - mu) = proj pt1 mu (fun i => phi (e i)) k := by
    intro k
    rw [hexp, proj]
    exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply]; ring
  have key0 :
      (phi ∈ (Submodule.span ℝ
          (Set.range fun k => pt0 k - mu)).dualAnnihilator) ↔
        ∀ k, proj pt0 mu (fun i => phi (e i)) k = 0 := by
    rw [mem_dualAnnihilator_span]
    constructor
    · intro h k
      rw [← hproj0 k]
      exact h _ (Set.mem_range_self k)
    · rintro h x ⟨k, rfl⟩
      rw [hproj0 k]
      exact h k
  have key1 :
      (phi ∈ (Submodule.span ℝ
          (Set.range fun k => pt1 k - mu)).dualAnnihilator) ↔
        ∀ k, proj pt1 mu (fun i => phi (e i)) k = 0 := by
    rw [mem_dualAnnihilator_span]
    constructor
    · intro h k
      rw [← hproj1 k]
      exact h _ (Set.mem_range_self k)
    · rintro h x ⟨k, rfl⟩
      rw [hproj1 k]
      exact h k
  rw [key0, key1]
  exact proj_eq_zero_congr₂ p0 p1 pt0 pt1 mu hp0 hp1 hcov _

/-- The affine subspace obtained by translating the centred support span by its
mean. -/
def centeredHull {ι' : Type*} (pt : ι' → Fin n → ℝ) (mu : Fin n → ℝ) :
    AffineSubspace ℝ (Fin n → ℝ) :=
  AffineSubspace.mk' mu (Submodule.span ℝ (Set.range fun k => pt k - mu))

/-- A normalized weighted mean lies in the affine span of its point family. -/
theorem weightedMean_mem_affineSpan
    {ι' : Type*} [Fintype ι'] (p : ι' → ℝ)
    (pt : ι' → Fin n → ℝ) (mu : Fin n → ℝ)
    (hnorm : ∑ k, p k = 1)
    (hmean : (fun j => ∑ k, p k * pt k j) = mu) :
    mu ∈ affineSpan ℝ (Set.range pt) := by
  classical
  have hmem := affineCombination_mem_affineSpan
    (s := (Finset.univ : Finset ι')) hnorm pt
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hnorm] at hmem
  have heq : (∑ k, p k • pt k) = mu := by
    rw [← hmean]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rwa [heq] at hmem

/-- If the chosen centre belongs to the affine span, translating the centred
linear span recovers the actual affine hull, not merely an upper bound. -/
theorem centeredHull_eq_affineSpan
    {ι' : Type*} (pt : ι' → Fin n → ℝ) (mu : Fin n → ℝ)
    (hmu : mu ∈ affineSpan ℝ (Set.range pt)) :
    centeredHull pt mu = affineSpan ℝ (Set.range pt) := by
  apply le_antisymm
  · intro q hq
    have hv : q - mu ∈ Submodule.span ℝ
        (Set.range fun k => pt k - mu) := hq
    have hspan : Submodule.span ℝ (Set.range fun k => pt k - mu) ≤
        (affineSpan ℝ (Set.range pt)).direction := by
      apply Submodule.span_le.2
      rintro v ⟨k, rfl⟩
      exact AffineSubspace.vsub_mem_direction
        (mem_affineSpan ℝ (Set.mem_range_self k)) hmu
    rw [← vsub_vadd q mu]
    exact AffineSubspace.vadd_mem_of_mem_direction (hspan hv) hmu
  · apply affineSpan_le.2
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self k)

/-- **Common affine-span theorem for differently sized supports.**

This is the geometric headline of Lemma 5.2 with all bookkeeping present:
normalization and the mean equations put `mu` in both affine hulls, while the
common covariance identifies their directions. -/
theorem affineSpan_eq_of_cov_eq₂
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (p0 : ι₀ → ℝ) (p1 : ι₁ → ℝ)
    (pt0 : ι₀ → Fin n → ℝ) (pt1 : ι₁ → Fin n → ℝ)
    (mu : Fin n → ℝ)
    (hp0 : ∀ k, 0 < p0 k) (hp1 : ∀ k, 0 < p1 k)
    (hnorm0 : ∑ k, p0 k = 1) (hnorm1 : ∑ k, p1 k = 1)
    (hmean0 : (fun j => ∑ k, p0 k * pt0 k j) = mu)
    (hmean1 : (fun j => ∑ k, p1 k * pt1 k j) = mu)
    (hcov : cov p0 pt0 mu = cov p1 pt1 mu) :
    affineSpan ℝ (Set.range pt0) = affineSpan ℝ (Set.range pt1) := by
  have hmu0 := weightedMean_mem_affineSpan p0 pt0 mu hnorm0 hmean0
  have hmu1 := weightedMean_mem_affineSpan p1 pt1 mu hnorm1 hmean1
  rw [← centeredHull_eq_affineSpan pt0 mu hmu0,
    ← centeredHull_eq_affineSpan pt1 mu hmu1]
  unfold centeredHull
  rw [span_eq_of_cov_eq₂ p0 p1 pt0 pt1 mu hp0 hp1 hcov]

/-! ## Non-vacuity

A weighted point set whose covariance form has a nontrivial kernel: two points
on a line, and the direction orthogonal to it.  Without an instance like this,
`quad_eq_zero_iff` could be a statement about a situation that never arises. -/

/-- Two points differing only in the first coordinate. -/
def twoPoints : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![1, 0]]

/-- The direction orthogonal to the line through them. -/
def orthDir : Fin 2 → ℝ := ![0, 1]

/-- Their mean. -/
noncomputable def twoMean : Fin 2 → ℝ := ![1/2, 0]

/-- The orthogonal direction annihilates the centred support, so the right-hand
side of `quad_eq_zero_iff` is satisfiable. -/
theorem orthDir_mem_kernel :
    ∀ k : Fin 2, proj twoPoints twoMean orthDir k = 0 := by
  intro k
  fin_cases k <;> simp [proj, twoPoints, twoMean, orthDir, Fin.sum_univ_two]

/-- A direction that does *not* annihilate it, so the condition has content. -/
theorem along_not_mem_kernel :
    proj twoPoints twoMean ![(1:ℝ), 0] 0 ≠ 0 := by
  norm_num [proj, twoPoints, twoMean, Fin.sum_univ_two]

end MainTheory.Covariance
