import QECC.ProjectorSupport

namespace QECC

open scoped BigOperators

noncomputable section

/-- Embed a bit string as its zero-one vector over the reals. -/
def bitVector {n : ℕ} (x : BitString n) : Fin n → ℝ :=
  fun j => bitReal (x j)

@[simp] theorem bitVector_apply {n : ℕ} (x : BitString n) (j : Fin n) :
    bitVector x j = bitReal (x j) :=
  rfl

/-- The image in real coordinate space of the positive support of a weight
function on bit strings. -/
def positiveSupportImage {n : ℕ} (p : BitString n → ℝ) :
    Set (Fin n → ℝ) :=
  bitVector '' {x | 0 < p x}

/-- Weighted expectation of the square of an affine functional. -/
def affineSquareExpectation {n : ℕ} (p : BitString n → ℝ)
    (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) : ℝ :=
  ∑ x : BitString n, p x * (f (bitVector x)) ^ 2

/-- The standard coordinate expansion of the zero-one vector associated to a
bit string. -/
theorem bitVector_eq_sum_single {n : ℕ} (x : BitString n) :
    bitVector x =
      ∑ j : Fin n, bitReal (x j) •
        (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
  funext i
  simp [bitVector, Pi.single_apply]

/-- An affine functional evaluated on a zero-one vector is its constant term
plus the corresponding linear combination of its coordinate coefficients. -/
theorem affine_apply_bitVector {n : ℕ}
    (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (x : BitString n) :
    f (bitVector x) =
      f 0 + ∑ j : Fin n,
        bitReal (x j) * f.linear (Pi.single j 1) := by
  have hmap := f.map_vadd (0 : Fin n → ℝ) (bitVector x)
  simp only [vadd_eq_add, add_zero] at hmap
  rw [hmap, bitVector_eq_sum_single]
  simp only [map_sum, LinearMapClass.map_smul]
  rw [add_comm]
  simp [smul_eq_mul]

/-- The expectation of the square of an affine functional depends only on the
total mass and the first and second coordinate moments. -/
theorem affineSquareExpectation_expansion {n : ℕ}
    (p : BitString n → ℝ) (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) :
    affineSquareExpectation p f =
      (f 0) ^ 2 * (∑ x : BitString n, p x) +
      2 * f 0 *
        (∑ i : Fin n, f.linear (Pi.single i 1) *
          (∑ x : BitString n, p x * bitReal (x i))) +
      ∑ i : Fin n, ∑ j : Fin n,
        f.linear (Pi.single i 1) * f.linear (Pi.single j 1) *
          (∑ x : BitString n,
            p x * bitReal (x i) * bitReal (x j)) := by
  classical
  let c : ℝ := f 0
  let w : Fin n → ℝ := fun i => f.linear (Pi.single i 1)
  have hpoint (x : BitString n) :
      p x * (f (bitVector x)) ^ 2 =
        p x * c ^ 2 +
        ∑ i : Fin n, 2 * c * w i * (p x * bitReal (x i)) +
        ∑ i : Fin n, ∑ j : Fin n,
          w i * w j * (p x * bitReal (x i) * bitReal (x j)) := by
    rw [affine_apply_bitVector]
    change p x * (c + ∑ j : Fin n, bitReal (x j) * w j) ^ 2 = _
    have hcross :
        (∑ i : Fin n, 2 * c * w i * (p x * bitReal (x i))) =
          2 * c * p x * (∑ i : Fin n, bitReal (x i) * w i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hquad :
        (∑ i : Fin n, ∑ j : Fin n,
          w i * w j * (p x * bitReal (x i) * bitReal (x j))) =
          p x * (∑ i : Fin n, bitReal (x i) * w i) ^ 2 := by
      rw [sq, Fintype.sum_mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hcross, hquad]
    ring
  unfold affineSquareExpectation
  simp_rw [hpoint, Finset.sum_add_distrib]
  change
    (∑ x : BitString n, p x * c ^ 2) +
        (∑ x : BitString n, ∑ i : Fin n,
          2 * c * w i * (p x * bitReal (x i))) +
        (∑ x : BitString n, ∑ i : Fin n, ∑ j : Fin n,
          w i * w j * (p x * bitReal (x i) * bitReal (x j))) = _
  have h0 :
      (∑ x : BitString n, p x * c ^ 2) =
        c ^ 2 * ∑ x : BitString n, p x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have h1 :
      (∑ x : BitString n, ∑ i : Fin n,
        2 * c * w i * (p x * bitReal (x i))) =
        2 * c * ∑ i : Fin n,
          w i * (∑ x : BitString n, p x * bitReal (x i)) := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    ring_nf
  have h2 :
      (∑ x : BitString n, ∑ i : Fin n, ∑ j : Fin n,
        w i * w j * (p x * bitReal (x i) * bitReal (x j))) =
        ∑ i : Fin n, ∑ j : Fin n,
          w i * w j *
            (∑ x : BitString n,
              p x * bitReal (x i) * bitReal (x j)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  rw [h0, h1, h2]

/-- Equal total mass and equal first and second coordinate moments imply equal
squared expectations for all affine functionals. -/
theorem affineSquareExpectation_eq_of_moments {n : ℕ}
    (p r : BitString n → ℝ)
    (hmass : (∑ x, p x) = ∑ x, r x)
    (hfirst : ∀ i : Fin n,
      (∑ x, p x * bitReal (x i)) =
        ∑ x, r x * bitReal (x i))
    (hsecond : ∀ i j : Fin n,
      (∑ x, p x * bitReal (x i) * bitReal (x j)) =
        ∑ x, r x * bitReal (x i) * bitReal (x j))
    (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) :
    affineSquareExpectation p f = affineSquareExpectation r f := by
  rw [affineSquareExpectation_expansion,
    affineSquareExpectation_expansion, hmass]
  simp_rw [hfirst, hsecond]

private theorem positiveSupport_nonempty_of_sum_eq_one {α : Type*}
    [Fintype α] (p : α → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x, p x = 1) : ({x | 0 < p x} : Set α).Nonempty := by
  by_contra hempty
  have hnpos (x : α) : ¬ 0 < p x := by
    intro hx
    exact hempty ⟨x, hx⟩
  have hzero (x : α) : p x = 0 :=
    le_antisymm (le_of_not_gt (hnpos x)) (hp x)
  simp only [hzero, Finset.sum_const_zero] at hsum
  norm_num at hsum

private theorem affine_zero_transfers_across_square_expectations
    {n : ℕ} (p r : BitString n → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hr : ∀ x, 0 ≤ r x)
    (hsquare : ∀ f : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      affineSquareExpectation p f = affineSquareExpectation r f)
    (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (hf : ∀ x, 0 < p x → f (bitVector x) = 0) :
    ∀ y, 0 < r y → f (bitVector y) = 0 := by
  have hpzero : affineSquareExpectation p f = 0 := by
    unfold affineSquareExpectation
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : 0 < p x
    · simp [hf x hx]
    · have hpx : p x = 0 := le_antisymm (le_of_not_gt hx) (hp x)
      simp [hpx]
  have hrzero : affineSquareExpectation r f = 0 := by
    rw [← hsquare f, hpzero]
  intro y hy
  have hterm : r y * (f (bitVector y)) ^ 2 = 0 := by
    have hnonneg : ∀ x ∈ (Finset.univ : Finset (BitString n)),
        0 ≤ r x * (f (bitVector x)) ^ 2 := by
      intro x _
      exact mul_nonneg (hr x) (sq_nonneg _)
    exact ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hrzero) y
      (Finset.mem_univ y)
  have hsquarezero : (f (bitVector y)) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hy)
  exact sq_eq_zero_iff.mp hsquarezero

/-- Strictly positive finite distributions with the same squared expectation
for every affine functional have the same affine span of their supports. -/
theorem affineSpan_positiveSupportImage_eq_of_affineSquareExpectation
    {n : ℕ} (p r : BitString n → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hr : ∀ x, 0 ≤ r x)
    (hpMass : ∑ x, p x = 1) (hrMass : ∑ x, r x = 1)
    (hsquare : ∀ f : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      affineSquareExpectation p f = affineSquareExpectation r f) :
    affineSpan ℝ (positiveSupportImage p) =
      affineSpan ℝ (positiveSupportImage r) := by
  let S := positiveSupportImage p
  let T := positiveSupportImage r
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := positiveSupport_nonempty_of_sum_eq_one p hp hpMass
    exact ⟨bitVector x, x, hx, rfl⟩
  have hT : T.Nonempty := by
    obtain ⟨x, hx⟩ := positiveSupport_nonempty_of_sum_eq_one r hr hrMass
    exact ⟨bitVector x, x, hx, rfl⟩
  have hST : affineSpan ℝ T ≤ affineSpan ℝ S := by
    apply affineSpan_le.2
    intro y hyT
    obtain ⟨x0, hx0S⟩ := hS
    have hv : y - x0 ∈ vectorSpan ℝ S := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
        (vectorSpan ℝ S) (y - x0)).mp
      intro phi hphi
      let f : (Fin n → ℝ) →ᵃ[ℝ] ℝ :=
        phi.toAffineMap - AffineMap.const ℝ (Fin n → ℝ) (phi x0)
      have hfS : ∀ x, 0 < p x → f (bitVector x) = 0 := by
        intro x hx
        have hbitS : bitVector x ∈ S := ⟨x, hx, rfl⟩
        have hvsub : bitVector x - x0 ∈ vectorSpan ℝ S := by
          rw [vectorSpan_eq_span_vsub_set_right ℝ hx0S]
          apply Submodule.subset_span
          exact ⟨bitVector x, hbitS, rfl⟩
        have hphiZero : phi (bitVector x - x0) = 0 :=
          (Submodule.mem_dualAnnihilator phi).mp hphi _ hvsub
        simpa [f, map_sub] using hphiZero
      have hfT := affine_zero_transfers_across_square_expectations
        p r hp hr hsquare f hfS
      obtain ⟨y0, hy0, rfl⟩ := hyT
      have hfy : f (bitVector y0) = 0 := hfT y0 hy0
      simpa [f, map_sub] using hfy
    have hx0Span : x0 ∈ affineSpan ℝ S := subset_affineSpan ℝ S hx0S
    have := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hx0Span hv
    simpa using this
  have hTS : affineSpan ℝ S ≤ affineSpan ℝ T := by
    apply affineSpan_le.2
    intro y hyS
    obtain ⟨x0, hx0T⟩ := hT
    have hv : y - x0 ∈ vectorSpan ℝ T := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
        (vectorSpan ℝ T) (y - x0)).mp
      intro phi hphi
      let f : (Fin n → ℝ) →ᵃ[ℝ] ℝ :=
        phi.toAffineMap - AffineMap.const ℝ (Fin n → ℝ) (phi x0)
      have hfT : ∀ x, 0 < r x → f (bitVector x) = 0 := by
        intro x hx
        have hbitT : bitVector x ∈ T := ⟨x, hx, rfl⟩
        have hvsub : bitVector x - x0 ∈ vectorSpan ℝ T := by
          rw [vectorSpan_eq_span_vsub_set_right ℝ hx0T]
          apply Submodule.subset_span
          exact ⟨bitVector x, hbitT, rfl⟩
        have hphiZero : phi (bitVector x - x0) = 0 :=
          (Submodule.mem_dualAnnihilator phi).mp hphi _ hvsub
        simpa [f, map_sub] using hphiZero
      have hreverse : ∀ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
          affineSquareExpectation r g = affineSquareExpectation p g :=
        fun g => (hsquare g).symm
      have hfS := affine_zero_transfers_across_square_expectations
        r p hr hp hreverse f hfT
      obtain ⟨y0, hy0, rfl⟩ := hyS
      have hfy : f (bitVector y0) = 0 := hfS y0 hy0
      simpa [f, map_sub] using hfy
    have hx0Span : x0 ∈ affineSpan ℝ T := subset_affineSpan ℝ T hx0T
    have := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hx0Span hv
    simpa using this
  exact le_antisymm hTS hST

namespace CodeProjector

variable {n K q d : ℕ} (C : CodeProjector n K)

/-- The affine span, in real zero-one coordinates, of an active sector's
actual computational support. -/
def actualSectorAffineSpan (a : Fin n → ZMod q)
    (b : C.ActiveResidue a) : AffineSubspace ℝ (Fin n → ℝ) :=
  affineSpan ℝ (bitVector '' C.actualSectorSupport a b)

/-- The binary monomial on a pair of coordinates is their ordinary product.
This includes the repeated-coordinate case, using `x_i^2 = x_i` for bits. -/
theorem binaryMonomialValue_pair (i j : Fin n) (x : BitString n) :
    binaryMonomialValue {i, j} x =
      bitReal (x i) * bitReal (x j) := by
  by_cases hij : i = j
  · subst j
    cases hxi : x i <;> simp [binaryMonomialValue, hxi]
  · rw [binaryMonomialValue, Finset.prod_pair hij]

/-- In a code of distance at least three, the normalized distributions of any
two active sectors give the same squared expectation to every real affine
functional of the bit coordinates. -/
theorem activeSector_affineSquareExpectation_eq_of_hasDistanceAtLeast
    [NeZero q] (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hd : C.HasDistanceAtLeast d) (hd3 : 3 ≤ d)
    (b c : C.ActiveResidue a)
    (f : (Fin n → ℝ) →ᵃ[ℝ] ℝ) :
    affineSquareExpectation (C.sectorDistribution a b) f =
      affineSquareExpectation (C.sectorDistribution a c) f := by
  apply affineSquareExpectation_eq_of_moments
  · rw [C.sum_sectorDistribution hq a hpres b,
      C.sum_sectorDistribution hq a hpres c]
  · intro i
    have hmom := C.sectorMoment_eq_of_hasDistanceAtLeast hq a hpres hd
      ({i} : Finset (Fin n)) (by simp; omega) b c
    simpa [binaryMonomialValue] using hmom
  · intro i j
    have hcard : ({i, j} : Finset (Fin n)).card < d := by
      have hpairs : ({i, j} : Finset (Fin n)).card ≤ 2 := by
        calc
          ({i, j} : Finset (Fin n)).card ≤
              ({j} : Finset (Fin n)).card + 1 :=
            Finset.card_insert_le i {j}
          _ = 2 := by simp
      omega
    have hmom := C.sectorMoment_eq_of_hasDistanceAtLeast hq a hpres hd
      ({i, j} : Finset (Fin n)) hcard b c
    simpa only [binaryMonomialValue_pair, mul_assoc] using hmom

/-- All active sectors of a code of distance at least three have the same
affine span of their actual zero-one supports. -/
theorem actualSectorAffineSpan_eq_of_hasDistanceAtLeast [NeZero q]
    (hq : 0 < q) (a : Fin n → ZMod q)
    (hpres : C.Preserves (phaseHom n q hq a))
    (hd : C.HasDistanceAtLeast d) (hd3 : 3 ≤ d)
    (b c : C.ActiveResidue a) :
    C.actualSectorAffineSpan a b = C.actualSectorAffineSpan a c := by
  apply affineSpan_positiveSupportImage_eq_of_affineSquareExpectation
  · exact C.sectorDistribution_nonneg hq a hpres b
  · exact C.sectorDistribution_nonneg hq a hpres c
  · exact C.sum_sectorDistribution hq a hpres b
  · exact C.sum_sectorDistribution hq a hpres c
  · exact C.activeSector_affineSquareExpectation_eq_of_hasDistanceAtLeast
      hq a hpres hd hd3 b c

end CodeProjector

end

end QECC
