import SixQubit.Orbit7CovariantAlgebra
import SixQubit.Orbit7Exceptional
import SixQubit.Orbit7Affine
import SixQubit.Orbit7ProjectorAlgebra
import SixQubit.Orbit7BoundaryPSD
import SixQubit.Orbit7BoundaryIsolated
import SixQubit.Orbit7PairRank

/-!
# Orbit 7: full-support endpoint to the target star

This module is downstream of the physical tangent, affine, and exceptional
vertex layers.  It contains the positive-semidefinite endpoint step in the
original spinor coordinates.  In particular, no basis or phase gauge is
chosen: parallelism to `u` is expressed by the covariant perpendicular
inner product.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize

noncomputable section

set_option maxHeartbeats 4000000

/-- On the full `K₅` support, the five vertex parameters representing a
tangent are pointwise unique.  This is the explicit kernel bridge needed to
identify the affine witness with the independently produced exceptional
witness; existential witnesses are never silently conflated. -/
theorem vertex_parameter_unique
    (x y : Fin 5 × Fin 5 → ℂ)
    (hfull : FullEdgeSupport x)
    (r q : Fin 5 → ℂ)
    (hr : ∀ e ∈ edgePairs, y e = (r e.1 + r e.2) * x e)
    (hq : ∀ e ∈ edgePairs, y e = (q e.1 + q e.2) * x e) :
    r = q := by
  have hp : ∀ e ∈ edgePairs, r e.1 + r e.2 = q e.1 + q e.2 := by
    intro e he
    have h := (hr e he).symm.trans (hq e he)
    exact mul_right_cancel₀ (hfull e he) h
  have h01 : r 0 + r 1 = q 0 + q 1 := hp (0,1) (by decide)
  have h02 : r 0 + r 2 = q 0 + q 2 := hp (0,2) (by decide)
  have h03 : r 0 + r 3 = q 0 + q 3 := hp (0,3) (by decide)
  have h04 : r 0 + r 4 = q 0 + q 4 := hp (0,4) (by decide)
  have h12 : r 1 + r 2 = q 1 + q 2 := hp (1,2) (by decide)
  funext i
  fin_cases i
  · change r 0 = q 0
    linear_combination (1/2 : ℂ) * (h01 + h02 - h12)
  · change r 1 = q 1
    linear_combination (1/2 : ℂ) * (h01 + h12 - h02)
  · change r 2 = q 2
    linear_combination (1/2 : ℂ) * (h02 + h12 - h01)
  · have h13 : r 1 + r 3 = q 1 + q 3 := hp (1,3) (by decide)
    change r 3 = q 3
    linear_combination (1/2 : ℂ) * (h03 + h13 - h01)
  · have h14 : r 1 + r 4 = q 1 + q 4 := hp (1,4) (by decide)
    change r 4 = q 4
    linear_combination (1/2 : ℂ) * (h04 + h14 - h01)

/-- Genuine full-support affine data with the exceptional vertex attached to
the *same* vertex witness `r`. -/
theorem physical_exceptional_affine_data
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d))
    (hind : extremeDet c d ≠ 0) :
    ∃ r q mu nu, AffineTangentData c d r q mu nu ∧
      ∃ s : Fin 5, ∃ R : ℂ, ∀ i, i ≠ s → r i = R := by
  rcases physical_affine_tangent_data c d hc hd hnc hnd hcode hfull hind with
    ⟨r, q, mu, nu, haff⟩
  have hHx := hafnians_zero c d hc hd hcode
  have hHy := physical_hafnian_y_zero_of_full_independent
    c d hc hd hnc hnd hcode hfull hind
  have ht : IsVertexTangent (xcoord c d) (ycoord c d) :=
    ⟨r, haff.y_vertex⟩
  rcases exceptional_vertex_of_full_tangent
      (xcoord c d) (ycoord c d) hfull hHx ht hHy with
    ⟨r', hr', s, R, hR⟩
  have hre : r = r' := vertex_parameter_unique
    (xcoord c d) (ycoord c d) hfull r r' haff.y_vertex hr'
  subst r'
  exact ⟨r, q, mu, nu, haff, s, R, hR⟩

private def familyK (c d : SS.State 6 ℂ)
    (E : Finset (Fin 5 × Fin 5)) : ℂ :=
  ∑ e ∈ E, (6 * xcoord c d e) * star (6 * xcoord c d e)

private def aLine (d : SS.State 6 ℂ) (t : ℂ) : Spinor :=
  fun i => vSpin d i + t * perpSpin (vSpin d) i

private def bLine (c : SS.State 6 ℂ) (p : ℂ) : Spinor :=
  fun i => -uSpin c i + star p * perpSpin (uSpin c) i

/-- Literal sums of the reconstructed physical edge spinors when a family
has constant tangent values `(t,p)`.  The same coefficient `familyK`
appears on both sides; this comes from the actual pair-cross reconstruction,
not an equal-weight ansatz. -/
private theorem physical_constant_family_matrices
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (hu : uMass c = 1/6) (hv : vMass d = 1/6)
    (E : Finset (Fin 5 × Fin 5)) (hsub : E ⊆ edgePairs)
    (t p : ℂ)
    (ht : ∀ e ∈ E, ycoord c d e = t * xcoord c d e)
    (hp : ∀ e ∈ E, zcoord c d e = p * xcoord c d e) :
    (∀ i j, (∑ e ∈ E, AMat c e i j) =
      familyK c d E * aLine d t i * star (aLine d t j)) ∧
    (∀ i j, (∑ e ∈ E, BMat d e i j) =
      familyK c d E * bLine c p i * star (bLine c p j)) := by
  have ha : ∀ e ∈ E, ∀ i,
      spinor c (aBase e.1 e.2) i =
        (6 * xcoord c d e) * aLine d t i := by
    intro e he i
    exact acoord_of_vertex_value c d hv e t (ht e he) i
  have hb : ∀ e ∈ E, ∀ i,
      spinor d (bBase e.1 e.2) i =
        (6 * star (xcoord c d e)) * bLine c p i := by
    intro e he i
    have heall := hsub he
    exact bcoord_of_vertex_value c d hu e p
      (paircross_projection c d hc hd hcode e heall) (hp e he) i
  constructor
  · intro i j
    unfold familyK
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    unfold AMat block outer
    rw [ha e he i, ha e he j]
    simp only [star_mul']
    ring
  · intro i j
    unfold familyK
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    unfold BMat block outer
    rw [hb e he i, hb e he j]
    simp only [star_mul', star_star]
    ring

/-- The exceptional-vertex conclusion has exactly two edge-sum values: one
on the exceptional star and one on its complementary `K₄`. -/
theorem exceptional_edge_sum_partition
    (r : Fin 5 → ℂ) (s : Fin 5) (R : ℂ)
    (hr : ∀ i, i ≠ s → r i = R) :
    (∀ e ∈ incidentPairs s, r e.1 + r e.2 = R + r s) ∧
      (∀ e ∈ nonincidentPairs s, r e.1 + r e.2 = 2 * R) := by
  constructor
  · intro e he
    rcases e with ⟨i, j⟩
    fin_cases s <;> fin_cases i <;> fin_cases j <;>
      simp [incidentPairs, edgePairs] at he ⊢ <;>
      simp_all <;> ring
  · intro e he
    rcases e with ⟨i, j⟩
    fin_cases s <;> fin_cases i <;> fin_cases j <;>
      simp [nonincidentPairs, edgePairs] at he ⊢ <;>
      simp_all <;> ring

private lemma spinor_outer_trace_full_target
    (f : SS.State 6 ℂ) (y : SS.BitString 6) :
    spinor f y 0 * star (spinor f y 0) +
        spinor f y 1 * star (spinor f y 1) = (spinMass f y : ℂ) := by
  unfold spinor spinMass
  change f y * star (f y) +
      f (SS.bxor y abit) * star (f (SS.bxor y abit)) =
        ((Complex.normSq (f y) +
          Complex.normSq (f (SS.bxor y abit)) : ℝ) : ℂ)
  rw [mul_comm (f y), mul_comm (f (SS.bxor y abit)),
    SixQubit.star_mul_self, SixQubit.star_mul_self]
  push_cast
  rfl

/-- A physical incident family of total mass `1/3`, all of whose spinors are
parallel to the extreme spinor `u` of mass `1/6`, has frame operator exactly
`2 U`.  This is a covariant, entrywise statement and uses the explicit
positive-semidefinite frame certificate `incident_outer_eq_two`. -/
theorem incident_star_eq_two_of_u_parallel
    (c : SS.State 6 ℂ) (s : Fin 5)
    (hu : uMass c = 1/6)
    (hdeg : degreeA c s = 1/3)
    (hparallel : ∀ e ∈ incidentPairs s,
      spinInner (perpSpin (uSpin c))
        (spinor c (aBase e.1 e.2)) = 0) :
    ∀ i j, starA c s i j = 2 * U c i j := by
  let E := incidentPairs s
  let a0 : (Fin 5 × Fin 5) → ℂ := fun e =>
    spinor c (aBase e.1 e.2) 0
  let a1 : (Fin 5 × Fin 5) → ℂ := fun e =>
    spinor c (aBase e.1 e.2) 1
  let u := uSpin c
  let v := perpSpin u
  have huC : u 0 * star (u 0) + u 1 * star (u 1) = (1/6 : ℂ) := by
    change uSpin c 0 * star (uSpin c 0) +
      uSpin c 1 * star (uSpin c 1) = (1/6 : ℂ)
    rw [show uSpin c 0 * star (uSpin c 0) +
        uSpin c 1 * star (uSpin c 1) = (uMass c : ℂ) by
      simpa [uSpin, uMass] using spinor_outer_trace_full_target c zero]
    rw [hu]
    norm_num
  have hvC : v 0 * star (v 0) + v 1 * star (v 1) = (1/6 : ℂ) := by
    dsimp [v]
    simp
    simpa [mul_comm, add_comm] using huC
  have huv : star (v 0) * u 0 + star (v 1) * u 1 = 0 := by
    dsimp [v]
    simp
    ring
  have haMass :
      (∑ e ∈ E, (a0 e * star (a0 e) + a1 e * star (a1 e))) =
        (1/3 : ℂ) := by
    calc
      _ = ∑ e ∈ incidentPairs s, (aMass c e.1 e.2 : ℂ) := by
        apply Finset.sum_congr rfl
        intro e he
        dsimp [E, a0, a1]
        simpa [aMass] using
          spinor_outer_trace_full_target c (aBase e.1 e.2)
      _ = (degreeA c s : ℂ) := by
        unfold degreeA
        push_cast
        rfl
      _ = (1/3 : ℂ) := by rw [hdeg]; norm_num
  have haOrth : ∀ e ∈ E,
      star (v 0) * a0 e + star (v 1) * a1 e = 0 := by
    intro e he
    simpa [E, a0, a1, v, spinInner] using hparallel e he
  have hout := SixQubit.Orbit7BoundaryPSD.incident_outer_eq_two
    E a0 a1 (u 0) (u 1) (v 0) (v 1)
    huC hvC huv haMass haOrth
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [starA, AMat, block, outer, U, u, uSpin, E, a0] using hout.1
  · simpa [starA, AMat, block, outer, U, u, uSpin, E, a0, a1] using hout.2.1
  · simpa [starA, AMat, block, outer, U, u, uSpin, E, a0, a1] using hout.2.2.1
  · simpa [starA, AMat, block, outer, U, u, uSpin, E, a1] using hout.2.2.2

/-- The covariant endpoint equation
`star(anchorC) * T + anchorD = 0` is exactly the statement that the
`a`-line with vertex value `T` is the `u` line.  This proves parallelism for
the actual physical spinors reconstructed from `xcoord,ycoord`. -/
theorem incident_u_parallel_of_anchor_endpoint
    (c d : SS.State 6 ℂ)
    (hu : uMass c = 1/6) (hv : vMass d = 1/6)
    (r : Fin 5 → ℂ) (s : Fin 5) (T : ℂ)
    (hr : ∀ e ∈ edgePairs,
      ycoord c d e = (r e.1 + r e.2) * xcoord c d e)
    (hstar : ∀ e ∈ incidentPairs s, r e.1 + r e.2 = T)
    (hend : star (anchorC c d) * T + anchorD c d = 0) :
    ∀ e ∈ incidentPairs s,
      spinInner (perpSpin (uSpin c))
        (spinor c (aBase e.1 e.2)) = 0 := by
  intro e he
  have heall : e ∈ edgePairs := incident_subset s he
  have ht : ycoord c d e = T * xcoord c d e := by
    rw [hr e heall, hstar e he]
  have hline (i : Fin 2) :
      vSpin d i + T * perpSpin (vSpin d) i =
        (anchorC c d - T * star (anchorD c d)) * uSpin c i := by
    rw [anchor_decomposition c d hu i,
      perp_anchor_decomposition c d hu i]
    have hz : anchorD c d + T * star (anchorC c d) = 0 := by
      linear_combination hend
    linear_combination (perpSpin (uSpin c) i) * hz
  have ha0 := acoord_of_vertex_value c d hv e T ht 0
  have ha1 := acoord_of_vertex_value c d hv e T ht 1
  rw [hline 0] at ha0
  rw [hline 1] at ha1
  unfold spinInner
  simp [perpSpin, ha0, ha1]
  ring

/-- Actual physical endpoint bridge.  Once the covariant projector algebra
identifies an exceptional star whose `a` spinors are parallel to `u`, the
genuine scalar moments and star identity force both target-star equations.
No rank, purity, or projector premise is inserted. -/
theorem targetStar_of_incident_u_parallel
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (s : Fin 5)
    (hparallel : ∀ e ∈ incidentPairs s,
      spinInner (perpSpin (uSpin c))
        (spinor c (aBase e.1 e.2)) = 0) :
    TargetStar c d := by
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, _hv, _hAt, _hBt, hdeg, _hedge⟩
  have hA := incident_star_eq_two_of_u_parallel c s hu (hdeg s).1 hparallel
  have hs := star_identity c d hc hd hcode s
  have hB : ∀ i j, starB d s i j = 2 * W d i j := by
    intro i j
    linear_combination hs i j - hA i j
  exact ⟨s, hA, hB⟩

/-- Endpoint-to-target wrapper in the exact exceptional-star interface. -/
theorem targetStar_of_anchor_endpoint
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (r : Fin 5 → ℂ) (s : Fin 5) (T : ℂ)
    (hr : ∀ e ∈ edgePairs,
      ycoord c d e = (r e.1 + r e.2) * xcoord c d e)
    (hstar : ∀ e ∈ incidentPairs s, r e.1 + r e.2 = T)
    (hend : star (anchorC c d) * T + anchorD c d = 0) :
    TargetStar c d := by
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, _hAt, _hBt, _hdeg, _hedge⟩
  exact targetStar_of_incident_u_parallel c d hc hd hnc hnd hcode s
    (incident_u_parallel_of_anchor_endpoint c d hu hv r s T
      hr hstar hend)

/-- A target star gives the literal rank-two two-qubit marginal required by
the structural part of the Orbit-7 theorem.  Both diagonal blocks are proved
to be nonzero from the genuine normalization/KL scalar normal form; rank two
is then the kernel theorem `twoOuterBlocks_rank`, not a purity heuristic. -/
theorem pairRankTwo_of_targetStar
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (htarget : TargetStar c d) :
    HasPairRankTwo c d := by
  rcases htarget with ⟨s, hA, hB⟩
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, _hAt, _hBt, _hdeg, _hedge⟩
  have hu0or : uSpin c 0 ≠ 0 ∨ uSpin c 1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    rcases hn with ⟨hu0, hu1⟩
    have hu' := hu
    change Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1) = 1 / 6 at hu'
    rw [hu0, hu1, Complex.normSq_zero] at hu'
    norm_num at hu'
  have hv0or : vSpin d 0 ≠ 0 ∨ vSpin d 1 ≠ 0 := by
    by_contra hn
    push_neg at hn
    rcases hn with ⟨hv0, hv1⟩
    have hv' := hv
    change Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) = 1 / 6 at hv'
    rw [hv0, hv1, Complex.normSq_zero] at hv'
    norm_num at hv'
  obtain ⟨iu, hiu⟩ : ∃ i : Fin 2, uSpin c i ≠ 0 := by
    rcases hu0or with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨iv, hiv⟩ : ∃ i : Fin 2, vSpin d i ≠ 0 := by
    rcases hv0or with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  refine ⟨s, ?_⟩
  have hmatrix : pairMarginal c d s =
      twoOuterBlocks (uSpin c) (vSpin d) 3 3 := by
    ext p q
    rcases p with ⟨i, pi⟩
    rcases q with ⟨j, qj⟩
    fin_cases pi <;> fin_cases qj <;>
      simp [pairMarginal, twoOuterBlocks, Matrix.blockDiagonal_apply,
        pairZeroBlock, pairOneBlock, scaledOuter,
        U, W, uSpin, vSpin, block, outer, hA, hB] <;> ring
  unfold PairRankTwoAt
  rw [hmatrix]
  exact twoOuterBlocks_rank (uSpin c) (vSpin d) 3 3 iu iv hiu hiv
    (by norm_num) (by norm_num)

/-- An entrywise sum of the two independent positive rank-one frames
`2 uu† + 3 vv†` cannot itself be a single rank-one frame.  The proof is the
literal `2 × 2` determinant identity `det = 6 |u∧v|²`. -/
theorem independent_frame_not_rank_one
    (u v w : Spinor) (K : ℂ)
    (hind : u 0 * v 1 - u 1 * v 0 ≠ 0)
    (hframe : ∀ i j,
      K * w i * star (w j) =
        2 * u i * star (u j) + 3 * v i * star (v j)) :
    False := by
  have h00 := hframe 0 0
  have h01 := hframe 0 1
  have h10 := hframe 1 0
  have h11 := hframe 1 1
  have hdet :
      (2 * u 0 * star (u 0) + 3 * v 0 * star (v 0)) *
          (2 * u 1 * star (u 1) + 3 * v 1 * star (v 1)) -
        (2 * u 0 * star (u 1) + 3 * v 0 * star (v 1)) *
          (2 * u 1 * star (u 0) + 3 * v 1 * star (v 0)) = 0 := by
    rw [← h00, ← h11, ← h01, ← h10]
    ring
  have hfactor :
      (2 * u 0 * star (u 0) + 3 * v 0 * star (v 0)) *
          (2 * u 1 * star (u 1) + 3 * v 1 * star (v 1)) -
        (2 * u 0 * star (u 1) + 3 * v 0 * star (v 1)) *
          (2 * u 1 * star (u 0) + 3 * v 1 * star (v 0)) =
        6 * (u 0 * v 1 - u 1 * v 0) *
          star (u 0 * v 1 - u 1 * v 0) := by
    simp only [star_sub, star_mul']
    ring
  rw [hfactor] at hdet
  exact (mul_ne_zero
    (mul_ne_zero (by norm_num) hind)
    (star_ne_zero.mpr hind)) hdet

/-- Every edge belongs either to the star of `s` or to its complementary
six-edge graph.  Kept as a kernel enumeration so endpoint partitions can be
used without a set-theoretic gap. -/
theorem edge_incident_or_nonincident (s : Fin 5)
    (e : Fin 5 × Fin 5) (he : e ∈ edgePairs) :
    e ∈ incidentPairs s ∨ e ∈ nonincidentPairs s := by
  rcases e with ⟨i, j⟩
  fin_cases s <;> fin_cases i <;> fin_cases j <;>
    simp [edgePairs, incidentPairs, nonincidentPairs] at he ⊢

/-- If all ten physical `a`-spinors have a common covariant line, the
genuine global frame would have rank one.  Independent anchors make its
determinant strictly nonzero, so this branch is impossible. -/
theorem uniform_acoor_line_impossible
    (c d : SS.State 6 ℂ)
    (hv : vMass d = 1/6)
    (data : PhysicalFullTangentData c d)
    (hind : anchorD c d ≠ 0)
    (T : ℂ)
    (hall : ∀ e ∈ edgePairs,
      ycoord c d e = T * xcoord c d e) :
    False := by
  let w : Spinor := fun i => vSpin d i + T * perpSpin (vSpin d) i
  let K : ℂ := ∑ e ∈ edgePairs,
    (6 * xcoord c d e) * star (6 * xcoord c d e)
  have ha : ∀ e ∈ edgePairs, ∀ i,
      spinor c (aBase e.1 e.2) i =
        (6 * xcoord c d e) * w i := by
    intro e he i
    exact acoord_of_vertex_value c d hv e T (hall e he) i
  have hsum : ∀ i j, sumA c i j = K * w i * star (w j) := by
    intro i j
    unfold sumA K
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e he
    unfold AMat block outer
    rw [ha e he i, ha e he j]
    simp only [star_mul']
    ring
  have hdet :
      uSpin c 0 * vSpin d 1 - uSpin c 1 * vSpin d 0 ≠ 0 := by
    intro hz
    apply hind
    unfold anchorD spinInner perpSpin
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      star_neg, star_star]
    linear_combination 6 * hz
  apply independent_frame_not_rank_one (uSpin c) (vSpin d) w K hdet
  intro i j
  calc
    K * w i * star (w j) = sumA c i j := (hsum i j).symm
    _ = 2 * U c i j + 3 * W d i j := data.frameA i j
    _ = 2 * uSpin c i * star (uSpin c j) +
        3 * vSpin d i * star (vSpin d j) := by
      simp [U, W, block, outer, uSpin, vSpin]
      ring

/-- The equal-value case `T=N` in the exceptional-vertex split is ruled out
by the preceding literal frame determinant. -/
theorem exceptional_equal_values_impossible
    (c d : SS.State 6 ℂ)
    (hv : vMass d = 1/6)
    (data : PhysicalFullTangentData c d)
    (hind : anchorD c d ≠ 0)
    (r : Fin 5 → ℂ) (s : Fin 5) (T N : ℂ)
    (hr : ∀ e ∈ edgePairs,
      ycoord c d e = (r e.1 + r e.2) * xcoord c d e)
    (hstar : ∀ e ∈ incidentPairs s, r e.1 + r e.2 = T)
    (hnon : ∀ e ∈ nonincidentPairs s, r e.1 + r e.2 = N)
    (hTN : T = N) :
    False := by
  apply uniform_acoor_line_impossible c d hv data hind T
  intro e he
  rw [hr e he]
  rcases edge_incident_or_nonincident s e he with hs | hn
  · rw [hstar e hs]
  · rw [hnon e hn, ← hTN]

/-- The mass-`1/2` analogue of the exact orthogonal-family frame lemma.
It is kept division-free because it is used at the complementary endpoint. -/
private theorem family_outer_eq_three
    {I : Type*} [DecidableEq I]
    (E : Finset I) (a0 a1 : I → ℂ)
    (u0 u1 v0 v1 : ℂ)
    (hu : u0 * star u0 + u1 * star u1 = (1 / 6 : ℂ))
    (hv : v0 * star v0 + v1 * star v1 = (1 / 6 : ℂ))
    (huv : star v0 * u0 + star v1 * u1 = 0)
    (haMass : (∑ e ∈ E,
      (a0 e * star (a0 e) + a1 e * star (a1 e))) = (1 / 2 : ℂ))
    (haOrth : ∀ e ∈ E, star v0 * a0 e + star v1 * a1 e = 0) :
    (∑ e ∈ E, a0 e * star (a0 e)) = 3 * (u0 * star u0) ∧
    (∑ e ∈ E, a0 e * star (a1 e)) = 3 * (u0 * star u1) ∧
    (∑ e ∈ E, a1 e * star (a0 e)) = 3 * (u1 * star u0) ∧
    (∑ e ∈ E, a1 e * star (a1 e)) = 3 * (u1 * star u1) := by
  have hsum0 :
      (∑ e ∈ E, (a0 e * star (a0 e) + a1 e * star (a1 e))) *
          (v0 * star v0) =
        (v0 * star v0 + v1 * star v1) *
          (∑ e ∈ E, a1 e * star (a1 e)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he =>
      (SixQubit.Block33.ortho2 v0 v1 (a0 e) (a1 e) (haOrth e he)).1
  have hsum1 :
      (∑ e ∈ E, (a0 e * star (a0 e) + a1 e * star (a1 e))) *
          (v0 * star v1) =
        -((v0 * star v0 + v1 * star v1) *
          (∑ e ∈ E, a0 e * star (a1 e))) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun e he =>
      (SixQubit.Block33.ortho2 v0 v1 (a0 e) (a1 e) (haOrth e he)).2.1
  have hsum2 :
      (∑ e ∈ E, (a0 e * star (a0 e) + a1 e * star (a1 e))) *
          (v1 * star v1) =
        (v0 * star v0 + v1 * star v1) *
          (∑ e ∈ E, a0 e * star (a0 e)) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e he =>
      (SixQubit.Block33.ortho2 v0 v1 (a0 e) (a1 e) (haOrth e he)).2.2
  rw [haMass, hv] at hsum0 hsum1 hsum2
  have hP11 : (∑ e ∈ E, a1 e * star (a1 e)) =
      3 * (v0 * star v0) := by
    linear_combination (-6) * hsum0
  have hP01 : (∑ e ∈ E, a0 e * star (a1 e)) =
      -3 * (v0 * star v1) := by
    linear_combination 6 * hsum1
  have hP00 : (∑ e ∈ E, a0 e * star (a0 e)) =
      3 * (v1 * star v1) := by
    linear_combination (-6) * hsum2
  have ho := SixQubit.Block33.ortho2 v0 v1 u0 u1 huv
  rw [hu, hv] at ho
  have hv00 : v0 * star v0 = u1 * star u1 := by
    linear_combination 6 * ho.1
  have hv01 : v0 * star v1 = -(u0 * star u1) := by
    linear_combination 6 * ho.2.1
  have hv11 : v1 * star v1 = u0 * star u0 := by
    linear_combination 6 * ho.2.2
  have h00 : (∑ e ∈ E, a0 e * star (a0 e)) =
      3 * (u0 * star u0) := by rw [hP00, hv11]
  have h01 : (∑ e ∈ E, a0 e * star (a1 e)) =
      3 * (u0 * star u1) := by
    rw [hP01, hv01]
    ring
  have h10 : (∑ e ∈ E, a1 e * star (a0 e)) =
      3 * (u1 * star u0) := by
    have hc := congrArg star h01
    simp only [star_sum, star_mul', star_star] at hc
    norm_num at hc
    simpa [mul_comm] using hc
  have h11 : (∑ e ∈ E, a1 e * star (a1 e)) =
      3 * (u1 * star u1) := by rw [hP11, hv00]
  exact ⟨h00, h01, h10, h11⟩

/-- A complementary six-edge family of mass `1/2`, parallel to the extreme
spinor `u`, has frame operator exactly `3U`. -/
theorem nonincident_eq_three_of_u_parallel
    (c : SS.State 6 ℂ) (s : Fin 5)
    (hu : uMass c = 1/6)
    (hAt : totalA c = 5/6)
    (hdeg : degreeA c s = 1/3)
    (hparallel : ∀ e ∈ nonincidentPairs s,
      spinInner (perpSpin (uSpin c))
        (spinor c (aBase e.1 e.2)) = 0) :
    ∀ i j, (∑ e ∈ nonincidentPairs s, AMat c e i j) =
      3 * U c i j := by
  let E := nonincidentPairs s
  let a0 : (Fin 5 × Fin 5) → ℂ := fun e =>
    spinor c (aBase e.1 e.2) 0
  let a1 : (Fin 5 × Fin 5) → ℂ := fun e =>
    spinor c (aBase e.1 e.2) 1
  let u := uSpin c
  let v := perpSpin u
  have huC : u 0 * star (u 0) + u 1 * star (u 1) = (1/6 : ℂ) := by
    change uSpin c 0 * star (uSpin c 0) +
      uSpin c 1 * star (uSpin c 1) = (1/6 : ℂ)
    rw [show uSpin c 0 * star (uSpin c 0) +
        uSpin c 1 * star (uSpin c 1) = (uMass c : ℂ) by
      simpa [uSpin, uMass] using spinor_outer_trace_full_target c zero]
    rw [hu]
    norm_num
  have hvC : v 0 * star (v 0) + v 1 * star (v 1) = (1/6 : ℂ) := by
    dsimp [v]
    simp
    simpa [mul_comm, add_comm] using huC
  have huv : star (v 0) * u 0 + star (v 1) * u 1 = 0 := by
    dsimp [v]
    simp
    ring
  have haMass :
      (∑ e ∈ E, (a0 e * star (a0 e) + a1 e * star (a1 e))) =
        (1/2 : ℂ) := by
    calc
      _ = ∑ e ∈ nonincidentPairs s, (aMass c e.1 e.2 : ℂ) := by
        apply Finset.sum_congr rfl
        intro e he
        dsimp [E, a0, a1]
        simpa [aMass] using
          spinor_outer_trace_full_target c (aBase e.1 e.2)
      _ = ((totalA c - degreeA c s : ℝ) : ℂ) := by
        rw [← nonincident_sum c s]
        push_cast
        rfl
      _ = (1/2 : ℂ) := by rw [hAt, hdeg]; norm_num
  have haOrth : ∀ e ∈ E,
      star (v 0) * a0 e + star (v 1) * a1 e = 0 := by
    intro e he
    simpa [E, a0, a1, v, spinInner] using hparallel e he
  have hout := family_outer_eq_three E a0 a1
    (u 0) (u 1) (v 0) (v 1) huC hvC huv haMass haOrth
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [AMat, block, outer, U, u, uSpin, E, a0] using hout.1
  · simpa [AMat, block, outer, U, u, uSpin, E, a0, a1] using hout.2.1
  · simpa [AMat, block, outer, U, u, uSpin, E, a0, a1] using hout.2.2.1
  · simpa [AMat, block, outer, U, u, uSpin, E, a1] using hout.2.2.2

private lemma matEval_outer_self_full_target (s a : Spinor) :
    matEval s (outer a) s =
      (Complex.normSq (spinInner s a) : ℂ) := by
  have hprod : matEval s (outer a) s =
      spinInner s a * spinInner a s := by
    unfold matEval outer spinInner
    simp only [Fin.sum_univ_two]
    ring
  rw [hprod, ← star_spinInner s a]
  rw [mul_comm, SixQubit.star_mul_self]

private lemma matEval_outer_full_target (s a t : Spinor) :
    matEval s (outer a) t = spinInner s a * spinInner a t := by
  unfold matEval outer spinInner
  simp only [Fin.sum_univ_two]
  ring

private lemma matEval_two_outer_full_target
    (s t a b : Spinor) (A B : ℂ) :
    matEval s (fun i j => A * outer a i j + B * outer b i j) t =
      A * spinInner s a * spinInner a t +
        B * spinInner s b * spinInner b t := by
  unfold matEval outer spinInner
  simp only [Fin.sum_univ_two]
  ring

private lemma covariant_basis_inner
    (u : Spinor) (hu : spinInner u u = (1/6 : ℂ))
    (a b : ℂ) :
    spinInner u (fun i => a * u i + b * perpSpin u i) = a / 6 ∧
    spinInner (perpSpin u) (fun i => a * u i + b * perpSpin u i) = b / 6 := by
  unfold spinInner at hu
  constructor
  · unfold spinInner perpSpin at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination a * hu
  · unfold spinInner perpSpin at ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      star_neg, star_star]
    linear_combination b * hu

private lemma aLine_covariant (c d : SS.State 6 ℂ)
    (hu : uMass c = 1/6) (t : ℂ) :
    ∀ i, aLine d t i =
      (anchorC c d - t * star (anchorD c d)) * uSpin c i +
        (anchorD c d + t * star (anchorC c d)) *
          perpSpin (uSpin c) i := by
  intro i
  unfold aLine
  rw [anchor_decomposition c d hu i,
    perp_anchor_decomposition c d hu i]
  ring

private lemma line_trace (d : SS.State 6 ℂ)
    (hv : vMass d = 1/6) (t : ℂ) :
    aLine d t 0 * star (aLine d t 0) +
        aLine d t 1 * star (aLine d t 1) =
      (1/6 : ℂ) * (1 + t * star t) := by
  have hvC : vSpin d 0 * star (vSpin d 0) +
      vSpin d 1 * star (vSpin d 1) = (1/6 : ℂ) := by
    rw [show vSpin d 0 * star (vSpin d 0) +
        vSpin d 1 * star (vSpin d 1) = (vMass d : ℂ) by
      simpa [vSpin, vMass] using
        spinor_outer_trace_full_target d activeAll]
    rw [hv]
    norm_num
  unfold aLine perpSpin
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, star_add,
    star_mul', star_neg, star_star]
  linear_combination (1 + t * star t) * hvC

/-- Actual constant-family star/nonstar matrix equations imply the two
cleared covariant projector entries.  The common edge coefficient is
eliminated using the exact physical family mass `k/6`. -/
theorem physical_family_projector_entries
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (hu : uMass c = 1/6) (hv : vMass d = 1/6)
    (E : Finset (Fin 5 × Fin 5)) (hsub : E ⊆ edgePairs)
    (k t p : ℂ) (hk : k ≠ 0)
    (ht : ∀ e ∈ E, ycoord c d e = t * xcoord c d e)
    (hp : ∀ e ∈ E, zcoord c d e = p * xcoord c d e)
    (hmass : (((∑ e ∈ E, aMass c e.1 e.2) : ℝ) : ℂ) = k / 6)
    (hframe : ∀ i j,
      (∑ e ∈ E, AMat c e i j) +
        (∑ e ∈ E, BMat d e i j) =
          k * (U c i j + W d i j)) :
    let cc := anchorC c d
    let dd := anchorD c d
    (((cc - t * star dd) * (star cc - star t * dd) + 1 =
        (1 + t * star t) * (1 + cc * star cc)) ∧
      ((dd + t * star cc) * (star cc - star t * dd) - star p =
        (1 + t * star t) * (dd * star cc))) ∧
    (star cc * star dd * t + cc * dd * star t +
        2 * cc * star cc * t * star t = 0 ∧
      cc * star p = star cc * t) := by
  dsimp
  let K := familyK c d E
  let aa := aLine d t
  let bb := bLine c p
  have hm := physical_constant_family_matrices c d hc hd hcode hu hv
    E hsub t p ht hp
  have hA := hm.1
  have hB := hm.2
  change ∀ i j, (∑ e ∈ E, AMat c e i j) =
    K * aa i * star (aa j) at hA
  change ∀ i j, (∑ e ∈ E, BMat d e i j) =
    K * bb i * star (bb j) at hB
  have htrace : ((∑ e ∈ E, aMass c e.1 e.2 : ℝ) : ℂ) =
      K * (aa 0 * star (aa 0) + aa 1 * star (aa 1)) := by
    calc
      _ = (∑ e ∈ E, AMat c e 0 0) +
          (∑ e ∈ E, AMat c e 1 1) := by
        push_cast
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e _he
        simpa [aMass, AMat, block, outer] using
          (spinor_outer_trace_full_target c (aBase e.1 e.2)).symm
      _ = K * (aa 0 * star (aa 0) + aa 1 * star (aa 1)) := by
        rw [hA 0 0, hA 1 1]
        dsimp [K, aa]
        ring
  have hK : K * (1 + t * star t) = k := by
    rw [hmass, line_trace d hv t] at htrace
    calc
      K * (1 + t * star t) =
          6 * (K * ((1/6 : ℂ) * (1 + t * star t))) := by ring
      _ = 6 * (k / 6) := by rw [← htrace]
      _ = k := by ring
  have huC : spinInner (uSpin c) (uSpin c) = (1/6 : ℂ) := by
    unfold spinInner
    have h := congrArg (fun r : ℝ => (r : ℂ)) hu
    push_cast at h
    simpa [uMass, spinMass, uSpin, spinor, ← SixQubit.star_mul_self]
      using h
  have haa : ∀ i, aa i =
      (anchorC c d - t * star (anchorD c d)) * uSpin c i +
        (anchorD c d + t * star (anchorC c d)) *
          perpSpin (uSpin c) i := aLine_covariant c d hu t
  have hua := (covariant_basis_inner (uSpin c) huC
    (anchorC c d - t * star (anchorD c d))
    (anchorD c d + t * star (anchorC c d))).1
  have hpua := (covariant_basis_inner (uSpin c) huC
    (anchorC c d - t * star (anchorD c d))
    (anchorD c d + t * star (anchorC c d))).2
  simp only [← haa] at hua hpua
  have hub := (covariant_basis_inner (uSpin c) huC (-1) (star p)).1
  have hpub := (covariant_basis_inner (uSpin c) huC (-1) (star p)).2
  have hub' : spinInner (uSpin c) bb = -1 / 6 := by
    simpa [bb, bLine] using hub
  have hpub' : spinInner (perpSpin (uSpin c)) bb = star p / 6 := by
    simpa [bb, bLine] using hpub
  have huvC : spinInner (uSpin c) (vSpin d) = anchorC c d / 6 := by
    unfold anchorC
    ring
  have hpuvC : spinInner (perpSpin (uSpin c)) (vSpin d) =
      anchorD c d / 6 := by
    unfold anchorD
    ring
  have hau : spinInner aa (uSpin c) =
      (star (anchorC c d) - star t * anchorD c d) / 6 := by
    rw [← star_spinInner, hua]
    simp
  have hbu : spinInner bb (uSpin c) = -1 / 6 := by
    rw [← star_spinInner, hub']
    norm_num
  have hvuC : spinInner (vSpin d) (uSpin c) =
      star (anchorC c d) / 6 := by
    rw [← star_spinInner, huvC]
    simp
  have hperpu : spinInner (perpSpin (uSpin c)) (uSpin c) = 0 :=
    perp_self (uSpin c)
  have hM : (fun i j => K * outer aa i j + K * outer bb i j) =
      (fun i j => k * outer (uSpin c) i j +
        k * outer (vSpin d) i j) := by
    funext i j
    unfold outer
    calc
      K * (aa i * star (aa j)) + K * (bb i * star (bb j)) =
          (∑ e ∈ E, AMat c e i j) +
            (∑ e ∈ E, BMat d e i j) := by
              rw [hA i j, hB i j]
              ring
      _ = k * (U c i j + W d i j) := hframe i j
      _ = k * (uSpin c i * star (uSpin c j)) +
          k * (vSpin d i * star (vSpin d j)) := by
            simp [U, W, block, outer, uSpin, vSpin]
            ring
  have h00 := congrArg (fun M : Mat2 =>
    matEval (uSpin c) M (uSpin c)) hM
  have h10 := congrArg (fun M : Mat2 =>
    matEval (perpSpin (uSpin c)) M (uSpin c)) hM
  dsimp only at h00 h10
  rw [matEval_two_outer_full_target, matEval_two_outer_full_target] at h00
  rw [matEval_two_outer_full_target, matEval_two_outer_full_target] at h10
  have h00' : K *
      ((anchorC c d - t * star (anchorD c d)) *
          (star (anchorC c d) - star t * anchorD c d) + 1) =
        k * (1 + anchorC c d * star (anchorC c d)) := by
    rw [hua, hau, hub', hbu, huC, huvC, hvuC] at h00
    field_simp at h00
    linear_combination h00
  have h10' : K *
      ((anchorD c d + t * star (anchorC c d)) *
          (star (anchorC c d) - star t * anchorD c d) - star p) =
        k * (anchorD c d * star (anchorC c d)) := by
    rw [hpua, hau, hpub', hbu, hperpu, huC, hpuvC, hvuC] at h10
    field_simp at h10
    linear_combination h10
  have h00clear :
      (anchorC c d - t * star (anchorD c d)) *
          (star (anchorC c d) - star t * anchorD c d) + 1 =
        (1 + t * star t) *
          (1 + anchorC c d * star (anchorC c d)) := by
    apply (mul_left_cancel₀ hk)
    calc
      k * ((anchorC c d - t * star (anchorD c d)) *
          (star (anchorC c d) - star t * anchorD c d) + 1) =
          (1 + t * star t) *
            (K * ((anchorC c d - t * star (anchorD c d)) *
              (star (anchorC c d) - star t * anchorD c d) + 1)) := by
            rw [← hK]
            ring
      _ = (1 + t * star t) *
          (k * (1 + anchorC c d * star (anchorC c d))) := by rw [h00']
      _ = k * ((1 + t * star t) *
          (1 + anchorC c d * star (anchorC c d))) := by ring
  have h10clear :
      (anchorD c d + t * star (anchorC c d)) *
          (star (anchorC c d) - star t * anchorD c d) - star p =
        (1 + t * star t) *
          (anchorD c d * star (anchorC c d)) := by
    apply (mul_left_cancel₀ hk)
    calc
      k * ((anchorD c d + t * star (anchorC c d)) *
          (star (anchorC c d) - star t * anchorD c d) - star p) =
          (1 + t * star t) *
            (K * ((anchorD c d + t * star (anchorC c d)) *
              (star (anchorC c d) - star t * anchorD c d) - star p)) := by
            rw [← hK]
            ring
      _ = (1 + t * star t) *
          (k * (anchorD c d * star (anchorC c d))) := by rw [h10']
      _ = k * ((1 + t * star t) *
          (anchorD c d * star (anchorC c d))) := by ring
  exact ⟨⟨h00clear, h10clear⟩,
    SixQubit.Orbit7ProjectorAlgebra.covariant_projector_entries
      (anchorC c d) (star (anchorC c d))
      (anchorD c d) (star (anchorD c d)) t (star t) (star p)
      (anchor_unit c d hu hv) h00clear h10clear⟩

private theorem edge_family_partition_sum
    (M : (Fin 5 × Fin 5) → ℂ) (s : Fin 5) :
    (∑ e ∈ edgePairs, M e) =
      (∑ e ∈ incidentPairs s, M e) +
        (∑ e ∈ nonincidentPairs s, M e) := by
  let pred : Fin 5 × Fin 5 → Prop := fun e => e.1 = s ∨ e.2 = s
  have h := Finset.sum_filter_add_sum_filter_not edgePairs pred M
  simpa [pred, incidentPairs, nonincidentPairs, not_or] using h.symm

/-- The actual exceptional star and its complementary six edges both obey
the cleared covariant projector equations, with exact scales `k=2,3`. -/
theorem exceptional_projector_entries
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (data : PhysicalFullTangentData c d)
    (r : Fin 5 → ℂ) (mu nu : ℂ) (s : Fin 5) (R : ℂ)
    (hr : ∀ e ∈ edgePairs,
      ycoord c d e = (r e.1 + r e.2) * xcoord c d e)
    (hzaff : ∀ e ∈ edgePairs,
      zcoord c d e = mu * ycoord c d e + nu * xcoord c d e)
    (hR : ∀ i, i ≠ s → r i = R) :
    let T := R + r s
    let N := 2 * R
    let pT := mu * T + nu
    let pN := mu * N + nu
    let cc := anchorC c d
    let dd := anchorD c d
    (((cc - T * star dd) * (star cc - star T * dd) + 1 =
        (1 + T * star T) * (1 + cc * star cc) ∧
      (dd + T * star cc) * (star cc - star T * dd) - star pT =
        (1 + T * star T) * (dd * star cc)) ∧
      (star cc * star dd * T + cc * dd * star T +
          2 * cc * star cc * T * star T = 0 ∧
        cc * star pT = star cc * T)) ∧
    (((cc - N * star dd) * (star cc - star N * dd) + 1 =
        (1 + N * star N) * (1 + cc * star cc) ∧
      (dd + N * star cc) * (star cc - star N * dd) - star pN =
        (1 + N * star N) * (dd * star cc)) ∧
      (star cc * star dd * N + cc * dd * star N +
          2 * cc * star cc * N * star N = 0 ∧
        cc * star pN = star cc * N)) := by
  dsimp
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, hAt, _hBt, hdeg, _hedge⟩
  have hstarT : ∀ e ∈ incidentPairs s,
      ycoord c d e = (R + r s) * xcoord c d e := by
    intro e he
    have heall := incident_subset s he
    rw [hr e heall]
    have hinc : e.1 = s ∨ e.2 = s := by
      simpa [incidentPairs, heall] using he
    rcases hinc with h1 | h2
    · have hre : r e.2 = R := hR e.2 (by
        intro hz
        have hlt : e.1 < e.2 := by simpa [edgePairs] using heall
        have hne : e.1 ≠ e.2 := ne_of_lt hlt
        exact hne (h1.trans hz.symm))
      rw [h1, hre]
      ring
    · have hre : r e.1 = R := hR e.1 (by
        intro hz
        have hlt : e.1 < e.2 := by simpa [edgePairs] using heall
        have hne : e.1 ≠ e.2 := ne_of_lt hlt
        exact hne (hz.trans h2.symm))
      rw [h2, hre]
  have hnonN : ∀ e ∈ nonincidentPairs s,
      ycoord c d e = (2 * R) * xcoord c d e := by
    intro e he
    have heall := nonincident_subset s he
    have hne : e.1 ≠ s ∧ e.2 ≠ s :=
      (Finset.mem_filter.mp he).2
    rw [hr e heall, hR e.1 hne.1, hR e.2 hne.2]
    ring
  have hstarP : ∀ e ∈ incidentPairs s,
      zcoord c d e = (mu * (R + r s) + nu) * xcoord c d e := by
    intro e he
    rw [hzaff e (incident_subset s he), hstarT e he]
    ring
  have hnonP : ∀ e ∈ nonincidentPairs s,
      zcoord c d e = (mu * (2 * R) + nu) * xcoord c d e := by
    intro e he
    rw [hzaff e (nonincident_subset s he), hnonN e he]
    ring
  have hstarMass : (((∑ e ∈ incidentPairs s,
      aMass c e.1 e.2 : ℝ) : ℂ)) = (2 : ℂ) / 6 := by
    change (degreeA c s : ℂ) = (2 : ℂ) / 6
    rw [(hdeg s).1]
    norm_num
  have hnonMass : (((∑ e ∈ nonincidentPairs s,
      aMass c e.1 e.2 : ℝ) : ℂ)) = (3 : ℂ) / 6 := by
    rw [nonincident_sum c s, hAt, (hdeg s).1]
    norm_num
  have hstarFrame : ∀ i j,
      (∑ e ∈ incidentPairs s, AMat c e i j) +
        (∑ e ∈ incidentPairs s, BMat d e i j) =
          (2 : ℂ) * (U c i j + W d i j) := by
    intro i j
    exact star_identity c d hc hd hcode s i j
  have hnonFrame : ∀ i j,
      (∑ e ∈ nonincidentPairs s, AMat c e i j) +
        (∑ e ∈ nonincidentPairs s, BMat d e i j) =
          (3 : ℂ) * (U c i j + W d i j) := by
    intro i j
    have hpa := edge_family_partition_sum (fun e => AMat c e i j) s
    have hpb := edge_family_partition_sum (fun e => BMat d e i j) s
    have hs := hstarFrame i j
    have ha := data.frameA i j
    have hb := data.frameB i j
    unfold sumA at ha
    unfold sumB at hb
    linear_combination ha + hb - hs - hpa - hpb
  constructor
  · exact physical_family_projector_entries c d hc hd hcode hu hv
      (incidentPairs s) (incident_subset s) 2 (R + r s)
      (mu * (R + r s) + nu) (by norm_num)
      hstarT hstarP hstarMass hstarFrame
  · exact physical_family_projector_entries c d hc hd hcode hu hv
      (nonincidentPairs s) (nonincident_subset s) 3 (2 * R)
      (mu * (2 * R) + nu) (by norm_num)
      hnonN hnonP hnonMass hnonFrame

private theorem exceptional_disjoint_value
    (h g : ℂ) (r q : Fin 5 → ℂ) (mu nu : ℂ)
    (s : Fin 5) (R : ℂ)
    (hdis : CovariantDisjoint h g r q)
    (haff : ∀ i j, q i + q j = mu * (r i + r j) + nu)
    (hR : ∀ i, i ≠ s → r i = R) :
    let T := R + r s
    let N := 2 * R
    let pT := mu * T + nu
    let pN := mu * N + nu
    star h * (T - N) + h * (pN - pT) +
      star g * (T * pN - N * pT) = 0 := by
  dsimp
  fin_cases s
  · have hd := hdis 0 1 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have r1 := hR 1 (by decide); have r2 := hR 2 (by decide)
    have r3 := hR 3 (by decide)
    rw [haff 0 1, haff 2 3, r1, r2, r3] at hd
    change star h * ((R + r 0) - 2 * R) +
      h * ((mu * (2 * R) + nu) - (mu * (R + r 0) + nu)) +
      star g * ((R + r 0) * (mu * (2 * R) + nu) -
        (2 * R) * (mu * (R + r 0) + nu)) = 0
    linear_combination hd
  · have hd := hdis 1 0 2 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have r0 := hR 0 (by decide); have r2 := hR 2 (by decide)
    have r3 := hR 3 (by decide)
    rw [haff 1 0, haff 2 3, r0, r2, r3] at hd
    change star h * ((R + r 1) - 2 * R) +
      h * ((mu * (2 * R) + nu) - (mu * (R + r 1) + nu)) +
      star g * ((R + r 1) * (mu * (2 * R) + nu) -
        (2 * R) * (mu * (R + r 1) + nu)) = 0
    linear_combination hd
  · have hd := hdis 2 0 1 3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have r0 := hR 0 (by decide); have r1 := hR 1 (by decide)
    have r3 := hR 3 (by decide)
    rw [haff 2 0, haff 1 3, r0, r1, r3] at hd
    change star h * ((R + r 2) - 2 * R) +
      h * ((mu * (2 * R) + nu) - (mu * (R + r 2) + nu)) +
      star g * ((R + r 2) * (mu * (2 * R) + nu) -
        (2 * R) * (mu * (R + r 2) + nu)) = 0
    linear_combination hd
  · have hd := hdis 3 0 1 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have r0 := hR 0 (by decide); have r1 := hR 1 (by decide)
    have r2 := hR 2 (by decide)
    rw [haff 3 0, haff 1 2, r0, r1, r2] at hd
    change star h * ((R + r 3) - 2 * R) +
      h * ((mu * (2 * R) + nu) - (mu * (R + r 3) + nu)) +
      star g * ((R + r 3) * (mu * (2 * R) + nu) -
        (2 * R) * (mu * (R + r 3) + nu)) = 0
    linear_combination hd
  · have hd := hdis 4 0 1 2 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    have r0 := hR 0 (by decide); have r1 := hR 1 (by decide)
    have r2 := hR 2 (by decide)
    rw [haff 4 0, haff 1 2, r0, r1, r2] at hd
    change star h * ((R + r 4) - 2 * R) +
      h * ((mu * (2 * R) + nu) - (mu * (R + r 4) + nu)) +
      star g * ((R + r 4) * (mu * (2 * R) + nu) -
        (2 * R) * (mu * (R + r 4) + nu)) = 0
    linear_combination hd

private theorem exceptional_covariant_circle_disjoint
    (c d : SS.State 6 ℂ)
    (r q : Fin 5 → ℂ) (mu nu : ℂ) (s : Fin 5) (R : ℂ)
    (hdis : CovariantDisjoint (extremeDet c d)
      (spinInner (uSpin c) (vSpin d)) r q)
    (haff : ∀ i j, q i + q j = mu * (r i + r j) + nu)
    (hR : ∀ i, i ≠ s → r i = R)
    (hphaseT : anchorC c d * star (mu * (R + r s) + nu) =
      star (anchorC c d) * (R + r s))
    (hphaseN : anchorC c d * star (mu * (2 * R) + nu) =
      star (anchorC c d) * (2 * R)) :
    let T := R + r s
    let N := 2 * R
    anchorC c d * anchorD c d * (star T - star N) +
      star (anchorC c d) * star (anchorD c d) * (N - T) +
      anchorC c d * star (anchorC c d) *
        (star T * N - star N * T) = 0 := by
  dsimp
  have hr := exceptional_disjoint_value
    (extremeDet c d) (spinInner (uSpin c) (vSpin d))
    r q mu nu s R hdis haff hR
  have hrs := congrArg star hr
  simp only [star_add, star_sub, star_mul', star_star, star_zero] at hrs
  unfold extremeDet at hrs
  unfold anchorC at hphaseT hphaseN
  unfold anchorC anchorD at ⊢
  simp only [star_add, star_mul'] at hrs hphaseT hphaseN ⊢
  have hs2 : star (2 : ℂ) = 2 := by norm_num
  have hs6 : star (6 : ℂ) = 6 := by norm_num
  simp_rw [hs2, hs6] at hrs hphaseT hphaseN ⊢
  simp only [map_add, map_mul, map_ofNat] at ⊢
  have hstarRing (z : ℂ) : (starRingEnd ℂ) z = star z := rfl
  simp_rw [hstarRing] at hrs hphaseT hphaseN ⊢
  linear_combination
    36 * spinInner (uSpin c) (vSpin d) * hrs
    + (6 * star (spinInner (perpSpin (uSpin c)) (vSpin d)) +
        6 * spinInner (uSpin c) (vSpin d) * (2 * star R)) * hphaseT
    + (-6 * star (spinInner (perpSpin (uSpin c)) (vSpin d)) -
        6 * spinInner (uSpin c) (vSpin d) *
          (star R + star (r s))) * hphaseN

theorem exceptional_three_cases
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d))
    (hind : extremeDet c d ≠ 0)
    (hC0 : anchorC c d ≠ 0)
    (r q : Fin 5 → ℂ) (mu nu : ℂ)
    (haff : AffineTangentData c d r q mu nu)
    (s : Fin 5) (R : ℂ) (hR : ∀ i, i ≠ s → r i = R) :
    let T := R + r s
    let N := 2 * R
    T = N ∨ star (anchorC c d) * T + anchorD c d = 0 ∨
      star (anchorC c d) * N + anchorD c d = 0 := by
  dsimp
  have pdata := physical_full_tangent_data c d hc hd hnc hnd hcode hfull
  have hp := exceptional_projector_entries c d hc hd hnc hnd hcode pdata
    r mu nu s R haff.y_vertex haff.z_affine hR
  have hcov := physical_covariant_disjoint c d hc hd hcode pdata hfull
    r q haff.y_vertex haff.z_vertex
  have hcircle := exceptional_covariant_circle_disjoint c d r q mu nu s R
    hcov haff.affine hR hp.1.2.2 hp.2.2.2
  have hD0 : anchorD c d ≠ 0 := by
    intro hz
    apply hind
    unfold anchorD at hz
    unfold extremeDet
    linear_combination (1/6 : ℂ) * hz
  exact SixQubit.Orbit7ProjectorAlgebra.covariant_disjoint_circle_three_cases
    (anchorC c d) (star (anchorC c d))
    (anchorD c d) (star (anchorD c d))
    (R + r s) (star (R + r s)) (2 * R) (star (2 * R))
    hC0 (star_ne_zero.mpr hC0) (star_ne_zero.mpr hD0)
    hp.1.2.1 hp.2.2.1 hcircle

private lemma matEval_nonincident_full_target
    (c : SS.State 6 ℂ) (s : Fin 5) (p : Spinor) :
    matEval p
        (fun i j => ∑ e ∈ nonincidentPairs s, AMat c e i j) p =
      ((∑ e ∈ nonincidentPairs s,
        Complex.normSq
          (spinInner p (spinor c (aBase e.1 e.2))) : ℝ) : ℂ) := by
  calc
    _ = ∑ e ∈ nonincidentPairs s, matEval p (AMat c e) p := by
      simp [matEval, Finset.mul_sum, Finset.sum_mul, Finset.sum_comm]
    _ = ∑ e ∈ nonincidentPairs s,
        (Complex.normSq
          (spinInner p (spinor c (aBase e.1 e.2))) : ℂ) := by
      apply Finset.sum_congr rfl
      intro e _he
      simpa [AMat, block] using
        matEval_outer_self_full_target p (spinor c (aBase e.1 e.2))
    _ = ((∑ e ∈ nonincidentPairs s,
        Complex.normSq
          (spinInner p (spinor c (aBase e.1 e.2))) : ℝ) : ℂ) := by
      push_cast
      rfl

/-- The complementary endpoint `star(anchorC) * N + anchorD = 0` is
impossible.  It would put all six nonincident `a`-spinors on the `u` line,
whose exact mass is `1/2`; their perpendicular-frame contribution would be
`3 |v∧u|²`, exceeding the genuine global total `2 |v∧u|²`. -/
theorem nonincident_anchor_endpoint_impossible
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (r : Fin 5 → ℂ) (s : Fin 5) (N : ℂ)
    (hr : ∀ e ∈ edgePairs,
      ycoord c d e = (r e.1 + r e.2) * xcoord c d e)
    (hnon : ∀ e ∈ nonincidentPairs s, r e.1 + r e.2 = N)
    (hind : anchorD c d ≠ 0)
    (hend : star (anchorC c d) * N + anchorD c d = 0) :
    False := by
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, hAt, _hBt, hdeg, _hedge⟩
  have hparallel : ∀ e ∈ nonincidentPairs s,
      spinInner (perpSpin (uSpin c))
        (spinor c (aBase e.1 e.2)) = 0 := by
    intro e he
    have heall : e ∈ edgePairs := nonincident_subset s he
    have ht : ycoord c d e = N * xcoord c d e := by
      rw [hr e heall, hnon e he]
    have hline (i : Fin 2) :
        vSpin d i + N * perpSpin (vSpin d) i =
          (anchorC c d - N * star (anchorD c d)) * uSpin c i := by
      rw [anchor_decomposition c d hu i,
        perp_anchor_decomposition c d hu i]
      have hz : anchorD c d + N * star (anchorC c d) = 0 := by
        linear_combination hend
      linear_combination (perpSpin (uSpin c) i) * hz
    have ha0 := acoord_of_vertex_value c d hv e N ht 0
    have ha1 := acoord_of_vertex_value c d hv e N ht 1
    rw [hline 0] at ha0
    rw [hline 1] at ha1
    unfold spinInner
    simp [perpSpin, ha0, ha1]
    ring
  have houter := nonincident_eq_three_of_u_parallel c s hu hAt
    (hdeg s).1 hparallel
  let p := perpSpin (vSpin d)
  have hmatrix :
      (fun i j => ∑ e ∈ nonincidentPairs s, AMat c e i j) =
        (fun i j => 3 * U c i j) := by
    funext i j
    exact houter i j
  have heval := congrArg (fun M : Mat2 => matEval p M p) hmatrix
  dsimp only at heval
  rw [matEval_nonincident_full_target] at heval
  have hright : matEval p (fun i j => 3 * U c i j) p =
      3 * (Complex.normSq (spinInner p (uSpin c)) : ℂ) := by
    have hscale : matEval p (fun i j => 3 * U c i j) p =
        3 * matEval p (U c) p := by
      unfold matEval
      simp only [Fin.sum_univ_two]
      ring
    rw [hscale]
    have hU : matEval p (U c) p =
        (Complex.normSq (spinInner p (uSpin c)) : ℂ) := by
      simpa [U, uSpin, block] using
        matEval_outer_self_full_target p (uSpin c)
    rw [hU]
  rw [hright] at heval
  have hevalR :
      (∑ e ∈ nonincidentPairs s,
        Complex.normSq
          (spinInner p (spinor c (aBase e.1 e.2)))) =
        3 * Complex.normSq (spinInner p (uSpin c)) := by
    exact_mod_cast heval
  have hwedge :
      vSpin d 0 * uSpin c 1 - vSpin d 1 * uSpin c 0 ≠ 0 := by
    intro hz
    apply hind
    unfold anchorD spinInner perpSpin
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, star_neg, star_star]
    linear_combination (-6) * hz
  have hnonR :
      (∑ e ∈ nonincidentPairs s,
        Complex.normSq
          (spinInner (perpSpin (vSpin d))
            (spinor c (aBase e.1 e.2)))) =
        3 * Complex.normSq
          (vSpin d 0 * uSpin c 1 - vSpin d 1 * uSpin c 0) := by
    simpa [p, perp_inner] using hevalR
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    (nonincident_subset s)
    (fun e heall hnot => Complex.normSq_nonneg
      (spinInner (perpSpin (vSpin d))
        (spinor c (aBase e.1 e.2))))
  rw [hnonR, perpendicular_frame_total c d hc hd hcode] at hsub
  have hpos : 0 < Complex.normSq
      (vSpin d 0 * uSpin c 1 - vSpin d 1 * uSpin c 0) :=
    Complex.normSq_pos.mpr hwedge
  nlinarith

/-- Complete independent, nonorthogonal full-support branch. -/
theorem full_support_nonorthogonal_target
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d))
    (hind : extremeDet c d ≠ 0)
    (hC0 : anchorC c d ≠ 0) :
    TargetStar c d := by
  rcases physical_exceptional_affine_data c d hc hd hnc hnd hcode hfull hind with
    ⟨r, q, mu, nu, haff, s, R, hR⟩
  have pdata := physical_full_tangent_data c d hc hd hnc hnd hcode hfull
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨_hu, hv, _hAt, _hBt, _hdeg, _hedge⟩
  have hD0 : anchorD c d ≠ 0 := by
    intro hz
    apply hind
    unfold anchorD at hz
    unfold extremeDet
    linear_combination (1/6 : ℂ) * hz
  rcases exceptional_edge_sum_partition r s R hR with ⟨hstar, hnon⟩
  rcases exceptional_three_cases c d hc hd hnc hnd hcode hfull hind hC0
      r q mu nu haff s R hR with hTN | hTend | hNend
  · exact (exceptional_equal_values_impossible c d hv pdata hD0
      r s (R + r s) (2 * R) haff.y_vertex hstar hnon hTN).elim
  · exact targetStar_of_anchor_endpoint c d hc hd hnc hnd hcode
      r s (R + r s) haff.y_vertex hstar hTend
  · exact (nonincident_anchor_endpoint_impossible c d hc hd hnc hnd hcode
      r s (2 * R) haff.y_vertex hnon hD0 hNend).elim

/-- The independent orthogonal-anchor full-support branch is impossible.
Crucially this uses the *uneliminated* physical `h10` projector entries;
the eliminated circle/phase equations alone are vacuous when `anchorC=0`. -/
theorem full_support_orthogonal_target
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d))
    (hind : extremeDet c d ≠ 0)
    (hCzero : anchorC c d = 0) :
    TargetStar c d := by
  rcases physical_exceptional_affine_data c d hc hd hnc hnd hcode hfull hind with
    ⟨r, q, mu, nu, haff, s, R, hR⟩
  have pdata := physical_full_tangent_data c d hc hd hnc hnd hcode hfull
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, _hAt, _hBt, _hdeg, _hedge⟩
  let T := R + r s
  let N := 2 * R
  let pT := mu * T + nu
  let pN := mu * N + nu
  have hp := exceptional_projector_entries c d hc hd hnc hnd hcode pdata
    r mu nu s R haff.y_vertex haff.z_affine hR
  have h10T := hp.1.1.2
  have h10N := hp.2.1.2
  change (anchorD c d + T * star (anchorC c d)) *
      (star (anchorC c d) - star T * anchorD c d) - star pT =
        (1 + T * star T) * (anchorD c d * star (anchorC c d)) at h10T
  change (anchorD c d + N * star (anchorC c d)) *
      (star (anchorC c d) - star N * anchorD c d) - star pN =
        (1 + N * star N) * (anchorD c d * star (anchorC c d)) at h10N
  have hpT : star pT = -(anchorD c d)^2 * star T := by
    rw [hCzero] at h10T
    simp only [star_zero, mul_zero, add_zero, zero_sub] at h10T
    linear_combination -h10T
  have hpN : star pN = -(anchorD c d)^2 * star N := by
    rw [hCzero] at h10N
    simp only [star_zero, mul_zero, add_zero, zero_sub] at h10N
    linear_combination -h10N
  have hg0 : spinInner (uSpin c) (vSpin d) = 0 := by
    unfold anchorC at hCzero
    linear_combination (1/6 : ℂ) * hCzero
  rcases haff.slope_parameter with ⟨lambda, hmu, _hnu⟩
  have hmu0 : mu = star (extremeDet c d) / extremeDet c d := by
    calc
      mu = star (extremeDet c d) / extremeDet c d +
          lambda * star (spinInner (uSpin c) (vSpin d)) := hmu
      _ = star (extremeDet c d) / extremeDet c d := by simp [hg0]
  have hmustar0 : star mu =
      extremeDet c d / star (extremeDet c d) := by
    rw [hmu0]
    simp
  have hunitD : anchorD c d * star (anchorD c d) = 1 := by
    have hu' := anchor_unit c d hu hv
    simpa [hCzero] using hu'
  have hmustar : star mu = (anchorD c d)^2 := by
    rw [hmustar0]
    have hsdet : star (extremeDet c d) ≠ 0 := star_ne_zero.mpr hind
    apply (div_eq_iff hsdet).2
    have hDdef : anchorD c d = 6 * extremeDet c d := rfl
    rw [hDdef] at hunitD ⊢
    norm_num [star_mul'] at hunitD
    have hstarRing (z : ℂ) : (starRingEnd ℂ) z = star z := rfl
    simp_rw [hstarRing] at hunitD
    linear_combination -(extremeDet c d) * hunitD
  have hpdiff : star pT - star pN =
      star mu * (star T - star N) := by
    dsimp [pT, pN, T, N]
    simp only [map_add, map_mul]
    ring
  rw [hpT, hpN, hmustar] at hpdiff
  have hz : 2 * (anchorD c d)^2 * (star T - star N) = 0 := by
    linear_combination -hpdiff
  have hD0 : anchorD c d ≠ 0 := by
    intro hzD
    apply hind
    unfold anchorD at hzD
    unfold extremeDet
    linear_combination (1/6 : ℂ) * hzD
  have hstarTN : star T = star N := by
    have hpref : 2 * (anchorD c d)^2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hD0)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hpref)
  have hTN : T = N := by
    have h := congrArg star hstarTN
    simpa using h
  rcases exceptional_edge_sum_partition r s R hR with ⟨hstar, hnon⟩
  exact (exceptional_equal_values_impossible c d hv pdata hD0
    r s T N haff.y_vertex hstar hnon hTN).elim

/-- Final independent-anchor full-support target, including the orthogonal
endpoint.  All premises are genuine physical hypotheses plus full support
and linear independence (`extremeDet ≠ 0`). -/
theorem full_support_independent_target
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d))
    (hind : extremeDet c d ≠ 0) :
    TargetStar c d := by
  by_cases hC : anchorC c d = 0
  · exact full_support_orthogonal_target c d hc hd hnc hnd hcode hfull hind hC
  · exact full_support_nonorthogonal_target c d hc hd hnc hnd hcode hfull hind hC

/-- The full-support independent branch supplies both conclusions required in
the manuscript: a target star and an actual rank-two two-qubit marginal. -/
theorem full_support_independent_target_and_pairRankTwo
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d))
    (hind : extremeDet c d ≠ 0) :
    TargetStar c d ∧ HasPairRankTwo c d := by
  have ht := full_support_independent_target c d hc hd hnc hnd hcode hfull hind
  exact ⟨ht, pairRankTwo_of_targetStar c d hc hd hnc hnd hcode ht⟩

end

end SixQubit.Orbit7Universal
