import SixQubit.Orbit7PhysicalTangent
import SixQubit.Orbit7PairSum
import SixQubit.Orbit7Exceptional

/-!
# Orbit 7: the covariant affine bridge on the full-support branch

This file is the middle algebraic bridge between the genuine physical
tangents in `Orbit7PhysicalTangent` and the exceptional-vertex algebra.
It treats the branch in which the two extreme spinors are linearly
independent.  No spinor gauge is chosen.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize

noncomputable section

set_option maxHeartbeats 4000000

/-- The determinant coordinate of the two extreme spinors. -/
def extremeDet (c d : SS.State 6 ℂ) : ℂ :=
  spinInner (perpSpin (uSpin c)) (vSpin d)

def edgeSum (r : Fin 5 → ℂ) (e : Fin 5 × Fin 5) : ℂ :=
  r e.1 + r e.2

/-- Gauge-covariant form of the manuscript's disjoint-edge equation. -/
def CovariantDisjoint (h g : ℂ) (r q : Fin 5 → ℂ) : Prop :=
  ∀ i j k l, i ≠ j → i ≠ k → i ≠ l →
    j ≠ k → j ≠ l → k ≠ l →
      star h * ((r i + r j) - (r k + r l)) +
        h * ((q k + q l) - (q i + q j)) +
        star g * ((r i + r j) * (q k + q l) -
          (r k + r l) * (q i + q j)) = 0

def affineH (h g : ℂ) (r : Fin 5 → ℂ) (i : Fin 5) : ℂ :=
  h / 2 + star g * r i

def affineDelta (h : ℂ) (r q : Fin 5 → ℂ) (i : Fin 5) : ℂ :=
  q i - (star h / h) * r i

/-- The covariant disjoint equation is exactly the five-vertex pair-sum
condition after the change of variables used in the manuscript. -/
theorem covariant_pair_sum (h g : ℂ) (r q : Fin 5 → ℂ)
    (hh : h ≠ 0) (hd : CovariantDisjoint h g r q) :
    PairSumCondition (affineH h g r) (affineDelta h r q) := by
  intro i j k l hij hik hil hjk hjl hkl
  have he := hd i j k l hij hik hil hjk hjl hkl
  have hz := congrArg (fun z : ℂ => 2 * h * z) he
  unfold affineH affineDelta
  field_simp [hh]
  ring_nf at hz ⊢
  exact hz

/-- Pair-sum collinearity gives affine edge sums.  The returned formulas for
`mu` and `nu` are retained for the subsequent proof that `mu` is nonzero. -/
theorem covariant_affine_edge_sums (h g : ℂ) (r q : Fin 5 → ℂ)
    (hh : h ≠ 0) (hd : CovariantDisjoint h g r q)
    (s : Fin 5) (hs : affineH h g r s ≠ 0) :
    ∃ lambda mu nu : ℂ,
      mu = star h / h + lambda * star g ∧
      nu = lambda * h ∧
      (∀ i, affineDelta h r q i = lambda * affineH h g r i) ∧
      (∀ i j, q i + q j = mu * (r i + r j) + nu) := by
  obtain ⟨lambda, hlam⟩ := pairSum_affine
    (affineH h g r) (affineDelta h r q)
    (covariant_pair_sum h g r q hh hd) s hs
  refine ⟨lambda, star h / h + lambda * star g, lambda * h,
    rfl, rfl, hlam, ?_⟩
  intro i j
  have hi := hlam i
  have hj := hlam j
  unfold affineDelta affineH at hi hj
  field_simp [hh] at hi hj ⊢
  linear_combination (1 / 2 : ℂ) * hi + (1 / 2 : ℂ) * hj

private lemma spinInner_self_star (v : Spinor) :
    star (spinInner v v) = spinInner v v := by
  unfold spinInner
  simp
  ring

/-- Reconstruction in the orthogonal frame `(v, perpSpin v)`. -/
private lemma spinor_reconstruct (v a : Spinor) :
    spinInner v v * a 0 =
        v 0 * spinInner v a - star (v 1) * spinInner (perpSpin v) a ∧
      spinInner v v * a 1 =
        v 1 * spinInner v a + star (v 0) * spinInner (perpSpin v) a := by
  constructor <;> simp [spinInner, perpSpin] <;> ring

/-- Coordinate expansion of one cross inner product.  It is stated before
specializing the six spinors to physical code blocks. -/
private lemma scaled_cross_formula
    (u v a b : Spinor) (x w t p : ℂ)
    (hva : spinInner v a = x)
    (hvpa : spinInner (perpSpin v) a = t * x)
    (hub : spinInner u b = -star w)
    (hupb : spinInner (perpSpin u) b = star (p * w)) :
    spinInner v v * spinInner u u * spinInner a b =
      star x * star w *
        (-star (spinInner u v) +
          star (spinInner (perpSpin u) v) * star p +
          spinInner (perpSpin u) v * star t +
          spinInner u v * star t * star p) := by
  rcases spinor_reconstruct v a with ⟨ha0, ha1⟩
  rcases spinor_reconstruct u b with ⟨hb0, hb1⟩
  rw [hva, hvpa] at ha0 ha1
  rw [hub, hupb] at hb0 hb1
  have hsv := spinInner_self_star v
  calc
    spinInner v v * spinInner u u * spinInner a b =
        star (spinInner v v * a 0) * (spinInner u u * b 0) +
          star (spinInner v v * a 1) * (spinInner u u * b 1) := by
            simp only [star_mul', hsv]
            unfold spinInner
            ring
    _ = star x * star w *
        (-star (spinInner u v) +
          star (spinInner (perpSpin u) v) * star p +
          spinInner (perpSpin u) v * star t +
          spinInner u v * star t * star p) := by
      rw [ha0, ha1, hb0, hb1]
      simp [spinInner, perpSpin]
      ring

/-- One genuine disjoint-edge KL row, expressed in the covariant tangent
ratios. -/
private theorem physical_covariant_edge
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (data : PhysicalFullTangentData c d)
    (hfull : FullEdgeSupport (xcoord c d))
    (r q : Fin 5 → ℂ)
    (hr : ∀ e ∈ edgePairs,
      ycoord c d e = edgeSum r e * xcoord c d e)
    (hq : ∀ e ∈ edgePairs,
      zcoord c d e = edgeSum q e * xcoord c d e)
    (e : Fin 5 × Fin 5) (he : e ∈ edgePairs)
    (f : Fin 5 × Fin 5) (hf : f ∈ nonincidentBoth e) :
    let h := extremeDet c d
    let g := spinInner (uSpin c) (vSpin d)
    star h * (edgeSum r e - edgeSum r f) +
      h * (edgeSum q f - edgeSum q e) +
      star g * (edgeSum r e * edgeSum q f -
        edgeSum r f * edgeSum q e) = 0 := by
  dsimp
  have hfe : f ∈ edgePairs := nonincidentBoth_subset e hf
  have hxE : xcoord c d e ≠ 0 := hfull e he
  have hxF : xcoord c d f ≠ 0 := hfull f hfe
  have hvaE : spinInner (vSpin d)
      (spinor c (aBase e.1 e.2)) = xcoord c d e := rfl
  have hvaF : spinInner (vSpin d)
      (spinor c (aBase f.1 f.2)) = xcoord c d f := rfl
  have hvpaE : spinInner (perpSpin (vSpin d))
      (spinor c (aBase e.1 e.2)) = edgeSum r e * xcoord c d e := by
    simpa [ycoord] using hr e he
  have hvpaF : spinInner (perpSpin (vSpin d))
      (spinor c (aBase f.1 f.2)) = edgeSum r f * xcoord c d f := by
    simpa [ycoord] using hr f hfe
  have hubE : spinInner (uSpin c)
      (spinor d (bBase e.1 e.2)) = -star (xcoord c d e) :=
    paircross_projection c d hc hd hcode e he
  have hubF : spinInner (uSpin c)
      (spinor d (bBase f.1 f.2)) = -star (xcoord c d f) := by
    exact paircross_projection c d hc hd hcode f hfe
  have hupbE : spinInner (perpSpin (uSpin c))
      (spinor d (bBase e.1 e.2)) = star (edgeSum q e * xcoord c d e) := by
    have hz := congrArg star (hq e he)
    simpa [zcoord, star_mul'] using hz
  have hupbF : spinInner (perpSpin (uSpin c))
      (spinor d (bBase f.1 f.2)) = star (edgeSum q f * xcoord c d f) := by
    have hz := congrArg star (hq f hfe)
    simpa [zcoord, star_mul'] using hz
  have hEF := scaled_cross_formula (uSpin c) (vSpin d)
    (spinor c (aBase e.1 e.2)) (spinor d (bBase f.1 f.2))
    (xcoord c d e) (xcoord c d f) (edgeSum r e) (edgeSum q f)
    hvaE hvpaE hubF hupbF
  have hFE := scaled_cross_formula (uSpin c) (vSpin d)
    (spinor c (aBase f.1 f.2)) (spinor d (bBase e.1 e.2))
    (xcoord c d f) (xcoord c d e) (edgeSum r f) (edgeSum q e)
    hvaF hvpaF hubE hupbE
  have hdis := data.disjoint_edges e he f hf
  have hscaled := congrArg
    (fun z : ℂ => spinInner (vSpin d) (vSpin d) *
      spinInner (uSpin c) (uSpin c) * z) hdis
  dsimp only at hscaled
  rw [hEF, hFE] at hscaled
  have hfac : star (xcoord c d e) * star (xcoord c d f) *
      star (star (extremeDet c d) * (edgeSum r e - edgeSum r f) +
        extremeDet c d * (edgeSum q f - edgeSum q e) +
        star (spinInner (uSpin c) (vSpin d)) *
          (edgeSum r e * edgeSum q f - edgeSum r f * edgeSum q e)) = 0 := by
    unfold extremeDet
    simp only [star_add, star_sub, star_mul', star_star]
    linear_combination hscaled
  have hfactor : star (xcoord c d e) * star (xcoord c d f) ≠ 0 :=
    mul_ne_zero (star_ne_zero.mpr hxE) (star_ne_zero.mpr hxF)
  have hz := (mul_eq_zero.mp hfac).resolve_left hfactor
  have := congrArg star hz
  simpa using this

private lemma canonEdge_mem (i j : Fin 5) (hij : i ≠ j) :
    canonEdge i j ∈ edgePairs := by
  unfold canonEdge edgePairs
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hlt : i < j
  · simp [hlt]
  · have hrev : j < i := by omega
    simp [hlt, hrev]

private lemma canonEdge_nonincident (i j k l : Fin 5)
    (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    canonEdge k l ∈ nonincidentBoth (canonEdge i j) := by
  unfold nonincidentBoth
  simp only [Finset.mem_filter]
  constructor
  · exact canonEdge_mem k l hkl
  · unfold canonEdge
    by_cases hijlt : i < j <;> by_cases hkllt : k < l <;>
      simp [hijlt, hkllt] <;> omega

private lemma edgeSum_canon (r : Fin 5 → ℂ) (i j : Fin 5) :
    edgeSum r (canonEdge i j) = r i + r j := by
  unfold edgeSum canonEdge
  by_cases hlt : i < j
  · simp [hlt]
  · simp [hlt, add_comm]

/-- The genuine disjoint-edge KL rows imply the complete covariant
pair-sum system for the actual vertex-tangent witnesses. -/
theorem physical_covariant_disjoint
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (data : PhysicalFullTangentData c d)
    (hfull : FullEdgeSupport (xcoord c d))
    (r q : Fin 5 → ℂ)
    (hr : ∀ e ∈ edgePairs,
      ycoord c d e = edgeSum r e * xcoord c d e)
    (hq : ∀ e ∈ edgePairs,
      zcoord c d e = edgeSum q e * xcoord c d e) :
    CovariantDisjoint (extremeDet c d)
      (spinInner (uSpin c) (vSpin d)) r q := by
  intro i j k l hij hik hil hjk hjl hkl
  have he := physical_covariant_edge c d hc hd hcode data hfull r q hr hq
    (canonEdge i j) (canonEdge_mem i j hij) (canonEdge k l)
    (canonEdge_nonincident i j k l hik hil hjk hjl hkl)
  simpa only [edgeSum_canon] using he

private lemma xycoord_normSq (c d : SS.State 6 ℂ)
    (e : Fin 5 × Fin 5) :
    Complex.normSq (xcoord c d e) + Complex.normSq (ycoord c d e) =
      vMass d * aMass c e.1 e.2 := by
  have h := SixQubit.Spinor.lagrange
    (vSpin d 0) (vSpin d 1)
    (spinor c (aBase e.1 e.2) 0) (spinor c (aBase e.1 e.2) 1)
  have hx : star (vSpin d 0) * spinor c (aBase e.1 e.2) 0 +
      star (vSpin d 1) * spinor c (aBase e.1 e.2) 1 =
        xcoord c d e := rfl
  have hy : vSpin d 0 * spinor c (aBase e.1 e.2) 1 -
      vSpin d 1 * spinor c (aBase e.1 e.2) 0 =
        ycoord c d e := by
    rw [ycoord, perp_inner]
  rw [hx, hy] at h
  simpa [vMass, aMass, spinMass, vSpin, spinor] using h

private theorem physical_xycoord_total
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    (∑ e ∈ edgePairs, Complex.normSq (xcoord c d e)) +
      (∑ e ∈ edgePairs, Complex.normSq (ycoord c d e)) = 5 / 36 := by
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨_hu, hv, hAt, _hBt, _hdeg, _hedge⟩
  calc
    (∑ e ∈ edgePairs, Complex.normSq (xcoord c d e)) +
        (∑ e ∈ edgePairs, Complex.normSq (ycoord c d e)) =
        ∑ e ∈ edgePairs,
          (Complex.normSq (xcoord c d e) + Complex.normSq (ycoord c d e)) := by
            rw [Finset.sum_add_distrib]
    _ = ∑ e ∈ edgePairs, vMass d * aMass c e.1 e.2 :=
      Finset.sum_congr rfl (fun e _he => xycoord_normSq c d e)
    _ = vMass d * totalA c := by
      unfold totalA
      rw [Finset.mul_sum]
    _ = 5 / 36 := by rw [hv, hAt]; norm_num

private theorem physical_extreme_gram
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    Complex.normSq (spinInner (uSpin c) (vSpin d)) +
      Complex.normSq (extremeDet c d) = 1 / 36 := by
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, _hAt, _hBt, _hdeg, _hedge⟩
  have h := SixQubit.Spinor.lagrange
    (uSpin c 0) (uSpin c 1) (vSpin d 0) (vSpin d 1)
  have hmassU : Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1) =
      uMass c := rfl
  have hmassV : Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) =
      vMass d := rfl
  have h' : Complex.normSq (spinInner (uSpin c) (vSpin d)) +
      Complex.normSq (extremeDet c d) =
        (Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1)) *
          (Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1)) := by
    simpa [spinInner, extremeDet, perp_inner, sub_eq_add_neg, add_comm] using h
  rw [hmassU, hmassV, hu, hv] at h'
  norm_num at h' ⊢
  exact h'

/-- In the independent-anchor branch, the first coordinates of the five
pair-sum vectors cannot all vanish.  This is the covariant replacement for
the manuscript's rank-two frame argument. -/
private theorem physical_affineH_exists
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hind : extremeDet c d ≠ 0)
    (r : Fin 5 → ℂ)
    (hr : ∀ e ∈ edgePairs,
      ycoord c d e = edgeSum r e * xcoord c d e) :
    ∃ s, affineH (extremeDet c d)
      (spinInner (uSpin c) (vSpin d)) r s ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hline : ∀ e ∈ edgePairs,
      star (spinInner (uSpin c) (vSpin d)) * ycoord c d e =
        -extremeDet c d * xcoord c d e := by
    intro e he
    have hi := hn e.1
    have hj := hn e.2
    unfold affineH at hi hj
    have ht : extremeDet c d +
        star (spinInner (uSpin c) (vSpin d)) * edgeSum r e = 0 := by
      unfold edgeSum
      linear_combination hi + hj
    rw [hr e he]
    linear_combination xcoord c d e * ht
  have hnorm : ∀ e ∈ edgePairs,
      Complex.normSq (spinInner (uSpin c) (vSpin d)) *
          Complex.normSq (ycoord c d e) =
        Complex.normSq (extremeDet c d) *
          Complex.normSq (xcoord c d e) := by
    intro e he
    have h := congrArg Complex.normSq (hline e he)
    simpa [Complex.normSq_mul, Complex.star_def, Complex.normSq_conj,
      Complex.normSq_neg] using h
  have hsum : Complex.normSq (spinInner (uSpin c) (vSpin d)) *
        (∑ e ∈ edgePairs, Complex.normSq (ycoord c d e)) =
      Complex.normSq (extremeDet c d) *
        (∑ e ∈ edgePairs, Complex.normSq (xcoord c d e)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun e he => hnorm e he)
  have hxy := physical_xycoord_total c d hc hd hnc hnd hcode
  have hx := xcoord_total c d hc hd hcode
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨_hu, hv, _hAt, _hBt, _hdeg, _hedge⟩
  rw [hv] at hx
  norm_num at hx
  have hsym : Complex.normSq (spinInner (vSpin d) (uSpin c)) =
      Complex.normSq (spinInner (uSpin c) (vSpin d)) := by
    rw [← star_spinInner]
    simp [Complex.normSq_conj]
  rw [hsym] at hx
  have hgh := physical_extreme_gram c d hc hd hnc hnd hcode
  have hpos : 0 < Complex.normSq (extremeDet c d) :=
    Complex.normSq_pos.mpr hind
  nlinarith [Complex.normSq_nonneg (spinInner (uSpin c) (vSpin d))]

private lemma affine_matEval_sum (s t : Spinor)
    (E : Finset (Fin 5 × Fin 5)) (M : (Fin 5 × Fin 5) → Mat2) :
    matEval s (fun i j => ∑ e ∈ E, M e i j) t =
      ∑ e ∈ E, matEval s (M e) t := by
  classical
  simp [matEval, Finset.mul_sum, Finset.sum_mul, Finset.sum_comm]

private lemma affine_matEval_block (s t : Spinor)
    (f : SS.State 6 ℂ) (y : SS.BitString 6) :
    matEval s (block f y) t =
      spinInner s (spinor f y) * spinInner (spinor f y) t := by
  unfold matEval block outer spinInner
  simp only [Fin.sum_univ_two]
  ring

/-- The second genuine global frame evaluated between `u` and `u⊥`.
This is the covariant form of the manuscript identity
`sum conj(x_e) z_e = -cd/3`. -/
private theorem physical_xzcoord_total
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (data : PhysicalFullTangentData c d) :
    (∑ e ∈ edgePairs, star (xcoord c d e) * zcoord c d e) =
      -2 * spinInner (uSpin c) (vSpin d) * star (extremeDet c d) := by
  let w := perpSpin (uSpin c)
  have hsum : matEval (uSpin c) (sumB d) w =
      ∑ e ∈ edgePairs, matEval (uSpin c) (BMat d e) w := by
    change matEval (uSpin c)
      (fun i j => ∑ e ∈ edgePairs, BMat d e i j) w = _
    exact affine_matEval_sum (uSpin c) w edgePairs (BMat d)
  have hterm : ∀ e ∈ edgePairs,
      matEval (uSpin c) (BMat d e) w =
        -star (xcoord c d e) * zcoord c d e := by
    intro e he
    have hp := paircross_projection c d hc hd hcode e he
    have hbw : spinInner (spinor d (bBase e.1 e.2)) w = zcoord c d e := by
      rw [← star_spinInner]
      rfl
    unfold BMat
    rw [affine_matEval_block, hp, hbw]
  have hleft : matEval (uSpin c) (sumB d) w =
      -(∑ e ∈ edgePairs, star (xcoord c d e) * zcoord c d e) := by
    rw [hsum]
    calc
      (∑ e ∈ edgePairs, matEval (uSpin c) (BMat d e) w) =
          ∑ e ∈ edgePairs,
            (-star (xcoord c d e) * zcoord c d e) :=
        Finset.sum_congr rfl (fun e he => hterm e he)
      _ = -(∑ e ∈ edgePairs,
          star (xcoord c d e) * zcoord c d e) := by
        simp only [neg_mul, Finset.sum_neg_distrib]
  have hmatrix : sumB d = fun i j => 3 * U c i j + 2 * W d i j := by
    funext i j
    exact data.frameB i j
  have heval := congrArg (fun M : Mat2 => matEval (uSpin c) M w) hmatrix
  have hright : matEval (uSpin c)
      (fun i j => 3 * U c i j + 2 * W d i j) w =
        2 * spinInner (uSpin c) (vSpin d) * star (extremeDet c d) := by
    unfold matEval U W block outer extremeDet w perpSpin uSpin vSpin spinInner
    simp [Fin.sum_univ_two]
    ring
  dsimp only at heval
  rw [hleft, hright] at heval
  linear_combination -heval

private theorem physical_affine_slope_ne
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (data : PhysicalFullTangentData c d)
    (hind : extremeDet c d ≠ 0)
    (r q : Fin 5 → ℂ)
    (hq : ∀ e ∈ edgePairs,
      zcoord c d e = edgeSum q e * xcoord c d e)
    (lambda mu nu : ℂ)
    (hmu : mu = star (extremeDet c d) / extremeDet c d +
      lambda * star (spinInner (uSpin c) (vSpin d)))
    (hnu : nu = lambda * extremeDet c d)
    (haff : ∀ i j, q i + q j = mu * (r i + r j) + nu) :
    mu ≠ 0 := by
  intro hmu0
  have hrel := hmu
  rw [hmu0] at hrel
  field_simp [hind] at hrel
  have hp : ∀ e ∈ edgePairs,
      star (spinInner (uSpin c) (vSpin d)) * zcoord c d e =
        -star (extremeDet c d) * xcoord c d e := by
    intro e he
    rw [hq e he]
    have heaff := haff e.1 e.2
    rw [hmu0, zero_mul, zero_add, hnu] at heaff
    change edgeSum q e = lambda * extremeDet c d at heaff
    rw [heaff]
    linear_combination -xcoord c d e * hrel
  have hterm : ∀ e ∈ edgePairs,
      star (spinInner (uSpin c) (vSpin d)) *
          (star (xcoord c d e) * zcoord c d e) =
        -star (extremeDet c d) *
          (Complex.normSq (xcoord c d e) : ℂ) := by
    intro e he
    have hz := hp e he
    rw [← SixQubit.star_mul_self (xcoord c d e)]
    linear_combination star (xcoord c d e) * hz
  have hsum : star (spinInner (uSpin c) (vSpin d)) *
        (∑ e ∈ edgePairs, star (xcoord c d e) * zcoord c d e) =
      -star (extremeDet c d) *
        (∑ e ∈ edgePairs, (Complex.normSq (xcoord c d e) : ℂ)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    simpa only [neg_mul] using hterm e he
  have hx := xcoord_total c d hc hd hcode
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨_hu, hv, _hAt, _hBt, _hdeg, _hedge⟩
  have hsym : Complex.normSq (spinInner (vSpin d) (uSpin c)) =
      Complex.normSq (spinInner (uSpin c) (vSpin d)) := by
    rw [← star_spinInner]
    simp [Complex.normSq_conj]
  rw [hv, hsym] at hx
  norm_num at hx
  have hxC := congrArg (fun t : ℝ => (t : ℂ)) hx
  push_cast at hxC
  have hxC' : (∑ e ∈ edgePairs,
      (Complex.normSq (xcoord c d e) : ℂ)) =
      2 * (star (spinInner (uSpin c) (vSpin d)) *
        spinInner (uSpin c) (vSpin d)) + 1 / 12 := by
    calc
      (∑ e ∈ edgePairs, (Complex.normSq (xcoord c d e) : ℂ)) =
          2 * (Complex.normSq (spinInner (uSpin c) (vSpin d)) : ℂ) +
            1 / 12 := hxC
      _ = 2 * (star (spinInner (uSpin c) (vSpin d)) *
          spinInner (uSpin c) (vSpin d)) + 1 / 12 := by
        rw [SixQubit.star_mul_self]
  have hxz := physical_xzcoord_total c d hc hd hcode data
  rw [hxz, hxC'] at hsum
  have hzero : star (extremeDet c d) * (1 / 12 : ℂ) = 0 := by
    linear_combination hsum
  have hstar : star (extremeDet c d) ≠ 0 := star_ne_zero.mpr hind
  exact hstar ((mul_eq_zero.mp hzero).resolve_right (by norm_num))

/-- The actual vertex witnesses and their nondegenerate affine relation.
All equations are restricted only to the ten canonical edges, which are the
coordinates present in the physical fibres. -/
structure AffineTangentData (c d : SS.State 6 ℂ)
    (r q : Fin 5 → ℂ) (mu nu : ℂ) : Prop where
  y_vertex : ∀ e ∈ edgePairs,
    ycoord c d e = edgeSum r e * xcoord c d e
  z_vertex : ∀ e ∈ edgePairs,
    zcoord c d e = edgeSum q e * xcoord c d e
  affine : ∀ i j, q i + q j = mu * (r i + r j) + nu
  slope_parameter : ∃ lambda,
    mu = star (extremeDet c d) / extremeDet c d +
        lambda * star (spinInner (uSpin c) (vSpin d)) ∧
      nu = lambda * extremeDet c d
  mu_ne : mu ≠ 0
  z_affine : ∀ e ∈ edgePairs,
    zcoord c d e = mu * ycoord c d e + nu * xcoord c d e
  yz_polar : ∀ v, PolarHafnian5 (ycoord c d) (zcoord c d) v = 0

/-- Public genuine-KL affine data for the full-support, independent-anchor
branch.  In particular, `r`, `q`, `mu`, and `nu` are conclusions, not chart
or rank assumptions. -/
theorem physical_affine_tangent_data
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d))
    (hind : extremeDet c d ≠ 0) :
    ∃ r q mu nu, AffineTangentData c d r q mu nu := by
  have data := physical_full_tangent_data c d hc hd hnc hnd hcode hfull
  rcases data.y_vertex with ⟨r, hr0⟩
  rcases data.z_vertex with ⟨q, hq0⟩
  have hr : ∀ e ∈ edgePairs,
      ycoord c d e = edgeSum r e * xcoord c d e := by
    intro e he
    simpa [edgeSum] using hr0 e he
  have hq : ∀ e ∈ edgePairs,
      zcoord c d e = edgeSum q e * xcoord c d e := by
    intro e he
    simpa [edgeSum] using hq0 e he
  have hdis := physical_covariant_disjoint c d hc hd hcode data hfull r q hr hq
  obtain ⟨s, hs⟩ := physical_affineH_exists c d hc hd hnc hnd hcode hind r hr
  obtain ⟨lambda, mu, nu, hmu, hnu, _hlambda, haff⟩ :=
    covariant_affine_edge_sums (extremeDet c d)
      (spinInner (uSpin c) (vSpin d)) r q hind hdis s hs
  have hmune := physical_affine_slope_ne c d hc hd hnc hnd hcode data hind
    r q hq lambda mu nu hmu hnu haff
  have hzaff : ∀ e ∈ edgePairs,
      zcoord c d e = mu * ycoord c d e + nu * xcoord c d e := by
    intro e he
    rw [hq e he, hr e he]
    have heq := haff e.1 e.2
    change edgeSum q e = mu * edgeSum r e + nu at heq
    rw [heq]
    ring
  exact ⟨r, q, mu, nu, {
    y_vertex := hr
    z_vertex := hq
    affine := haff
    slope_parameter := ⟨lambda, hmu, hnu⟩
    mu_ne := hmune
    z_affine := hzaff
    yz_polar := data.yz_polar
  }⟩

/-- The exact `H_i(y)=0` conclusion consumed by the exceptional-vertex
module, derived here from the genuine KL hypotheses on the independent
full-support branch. -/
theorem physical_hafnian_y_zero_of_full_independent
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d))
    (hind : extremeDet c d ≠ 0) :
    ∀ v, Hafnian5 (ycoord c d) v = 0 := by
  rcases physical_affine_tangent_data c d hc hd hnc hnd hcode hfull hind with
    ⟨r, q, mu, nu, data⟩
  let z' : Fin 5 × Fin 5 → ℂ := fun e =>
    if e ∈ edgePairs then zcoord c d e
    else mu * ycoord c d e + nu * xcoord c d e
  have hzaff : ∀ e, z' e = mu * ycoord c d e + nu * xcoord c d e := by
    intro e
    by_cases he : e ∈ edgePairs
    · simp [z', he, data.z_affine e he]
    · simp [z', he]
  have hyz : ∀ v, PolarHafnian5 (ycoord c d) z' v = 0 := by
    intro v
    have h := data.yz_polar v
    fin_cases v <;> simp [PolarHafnian5, z', edgePairs] at h ⊢ <;> exact h
  have hxy := (physical_polar_equations c d hc hd hcode).1
  exact hafnian_y_zero_of_affine_polar
    (xcoord c d) (ycoord c d) z' mu nu hzaff data.mu_ne hxy hyz

end

end SixQubit.Orbit7Universal
