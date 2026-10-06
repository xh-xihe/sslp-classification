import SixQubit.Orbit7Boundary
import SixQubit.Orbit7BoundaryPSD

/-!
# Orbit 7 universal converse, V: the isolated-support branch

This file closes the only positive-semidefinite branch of the boundary
classification without choosing a spinor basis.  The complementary spinor
`perpSpin v` is covariant and all estimates are exact identities in `ℂ²`.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize

noncomputable section

/-- The covariant perpendicular spinor `(-conj v₁, conj v₀)`. -/
def perpSpin (v : Spinor) : Spinor := ![-star (v 1), star (v 0)]

@[simp] lemma perpSpin_zero (v : Spinor) : perpSpin v 0 = -star (v 1) := rfl
@[simp] lemma perpSpin_one (v : Spinor) : perpSpin v 1 = star (v 0) := rfl

lemma perp_inner (v a : Spinor) :
    spinInner (perpSpin v) a = v 0 * a 1 - v 1 * a 0 := by
  unfold spinInner
  simp
  ring

lemma perp_self (v : Spinor) : spinInner (perpSpin v) v = 0 := by
  rw [perp_inner]
  ring

private lemma matEval_sum_local (s t : Spinor) (E : Finset (Fin 5 × Fin 5))
    (M : (Fin 5 × Fin 5) → Mat2) :
    matEval s (fun i j => ∑ e ∈ E, M e i j) t =
      ∑ e ∈ E, matEval s (M e) t := by
  classical
  simp [matEval, Finset.mul_sum, Finset.sum_mul, Finset.sum_comm]

private lemma matEval_outer_local (s a t : Spinor) :
    matEval s (fun i j => a i * star (a j)) t =
      spinInner s a * spinInner a t := by
  unfold matEval spinInner
  simp only [Fin.sum_univ_two]
  ring

private lemma matEval_block_local (s : Spinor) (f : SS.State 6 ℂ)
    (y : SS.BitString 6) :
    matEval s (block f y) s =
      (Complex.normSq (spinInner s (spinor f y)) : ℂ) := by
  rw [show block f y = fun i j => spinor f y i * star (spinor f y j) by rfl,
    matEval_outer_local, ← star_spinInner s (spinor f y)]
  rw [mul_comm, SixQubit.star_mul_self]

private lemma matEval_linear_local (s : Spinor) (M N : Mat2) (a b : ℂ) :
    matEval s (fun i j => a * M i j + b * N i j) s =
      a * matEval s M s + b * matEval s N s := by
  unfold matEval
  simp only [Fin.sum_univ_two]
  ring

private lemma matEval_sumA_local (c : SS.State 6 ℂ) (s : Spinor) :
    matEval s (sumA c) s =
      ((∑ e ∈ edgePairs,
        Complex.normSq (spinInner s (spinor c (aBase e.1 e.2))) : ℝ) : ℂ) := by
  unfold sumA AMat
  rw [matEval_sum_local]
  push_cast
  exact Finset.sum_congr rfl (fun e he => by rw [matEval_block_local])

/-- The global frame identity evaluated on the covariant perpendicular
spinor.  This is the exact PSD quantity used in the isolated branch. -/
theorem perpendicular_frame_total (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    (∑ e ∈ edgePairs,
      Complex.normSq
        (spinInner (perpSpin (vSpin d)) (spinor c (aBase e.1 e.2)))) =
      2 * Complex.normSq
        (vSpin d 0 * uSpin c 1 - vSpin d 1 * uSpin c 0) := by
  let w := perpSpin (vSpin d)
  have hf := (global_frames c d hc hd hcode).1
  have hmat : matEval w (sumA c) w =
      matEval w (fun i j => 2 * U c i j + 3 * W d i j) w := by
    apply congrArg (fun M : Mat2 => matEval w M w)
    funext i j
    exact hf i j
  rw [matEval_sumA_local, matEval_linear_local] at hmat
  unfold U W at hmat
  rw [matEval_block_local, matEval_block_local] at hmat
  have hwu : spinInner w (spinor c zero) =
      vSpin d 0 * spinor c zero 1 - vSpin d 1 * spinor c zero 0 := by
    simpa [uSpin] using perp_inner (vSpin d) (uSpin c)
  have hwv : spinInner w (spinor d activeAll) = 0 := by
    simpa [vSpin] using perp_self (vSpin d)
  rw [hwu, hwv, Complex.normSq_zero] at hmat
  norm_num at hmat
  dsimp [w] at hmat
  have hr :
      (∑ e ∈ edgePairs,
        Complex.normSq
          (spinInner (perpSpin (vSpin d)) (spinor c (aBase e.1 e.2)))) =
        2 * Complex.normSq
          (vSpin d 0 * c (SS.bxor abit zero) - vSpin d 1 * c zero) := by
    exact_mod_cast hmat
  simpa [uSpin, spinor] using hr

private lemma adj_comm (g : SixQubit.Orbit7Mask.Mask) (i j : Fin 5) :
    SixQubit.Orbit7Mask.Adj g i j ↔ SixQubit.Orbit7Mask.Adj g j i := by
  fin_cases i <;> fin_cases j <;>
    simp [SixQubit.Orbit7Mask.Adj, SixQubit.Orbit7Mask.edge]

private lemma isolated_xcoord_zero (c d : SS.State 6 ℂ) (s : Fin 5)
    (hisol : ∀ t, t ≠ s →
      ¬ SixQubit.Orbit7Mask.Adj (supportMask (xcoord c d)) s t) :
    ∀ e ∈ incidentPairs s, xcoord c d e = 0 := by
  intro e he
  have heall : e ∈ edgePairs := incident_subset s he
  have hinc : e.1 = s ∨ e.2 = s := by
    simpa [incidentPairs, heall] using he
  have hne : e.1 ≠ e.2 := by
    rcases e with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp_all [edgePairs]
  by_contra hx
  have hadj : SixQubit.Orbit7Mask.Adj
      (supportMask (xcoord c d)) e.1 e.2 :=
    (supportMask_adj (xcoord c d) e heall).2 hx
  rcases hinc with hfirst | hsecond
  · apply hisol e.2
      (by intro heq; exact hne (hfirst.trans heq.symm))
    rw [← hfirst]
    exact hadj
  · apply hisol e.1
      (by intro heq; exact hne (heq.trans hsecond.symm))
    rw [← hsecond]
    exact (adj_comm _ _ _).1 hadj

private lemma perpendicular_incident_term (c d : SS.State 6 ℂ)
    (e : Fin 5 × Fin 5) (hv : vMass d = 1/6)
    (hx : xcoord c d e = 0) :
    Complex.normSq
        (spinInner (perpSpin (vSpin d)) (spinor c (aBase e.1 e.2))) =
      (1/6) * aMass c e.1 e.2 := by
  let a := spinor c (aBase e.1 e.2)
  let v := vSpin d
  have hL := SixQubit.Spinor.lagrange (v 0) (v 1) (a 0) (a 1)
  have hx' : spinInner v a = 0 := by
    simpa [v, a, xcoord] using hx
  have hv' : Complex.normSq (v 0) + Complex.normSq (v 1) = 1/6 := by
    simpa [v, vSpin, vMass, spinMass] using hv
  change Complex.normSq (spinInner v a) +
      Complex.normSq (v 0 * a 1 - v 1 * a 0) =
        (Complex.normSq (v 0) + Complex.normSq (v 1)) *
          (Complex.normSq (a 0) + Complex.normSq (a 1)) at hL
  rw [hx', Complex.normSq_zero, hv'] at hL
  rw [perp_inner]
  simpa [a, aMass, spinMass] using hL

private lemma spinor_outer_trace (f : SS.State 6 ℂ) (y : SS.BitString 6) :
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

/-- An isolated support vertex forces exactly the rank-two-pair star target.
The proof exposes the nonnegative complementary frame sum, uses exact
two-dimensional Parseval/Lagrange algebra to kill the overlap, and then
identifies all four matrix entries.  No basis chart is assumed. -/
theorem isolated_target (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hisol : SixQubit.Orbit7Mask.Isolated
      (supportMask (xcoord c d))) :
    TargetStar c d := by
  rcases hisol with ⟨s, hs⟩
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, hAt, hBt, hdeg, hedge⟩
  have hxzero := isolated_xcoord_zero c d s hs
  have hinc :
      (∑ e ∈ incidentPairs s,
        Complex.normSq
          (spinInner (perpSpin (vSpin d)) (spinor c (aBase e.1 e.2)))) =
        (1/18 : ℝ) := by
    calc
      _ = ∑ e ∈ incidentPairs s, (1/6) * aMass c e.1 e.2 :=
        Finset.sum_congr rfl (fun e he =>
          perpendicular_incident_term c d e hv (hxzero e he))
      _ = (1/6) * degreeA c s := by
        unfold degreeA
        rw [Finset.mul_sum]
      _ = 1/18 := by rw [(hdeg s).1]; norm_num
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (incident_subset s)
    (fun e heall hnot => Complex.normSq_nonneg
      (spinInner (perpSpin (vSpin d)) (spinor c (aBase e.1 e.2))))
  rw [hinc, perpendicular_frame_total c d hc hd hcode] at hsub
  have hu' : Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1) =
      (1/6 : ℝ) := by
    simpa [uSpin, uMass, spinMass] using hu
  have hv' : Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) =
      (1/6 : ℝ) := by
    simpa [vSpin, vMass, spinMass] using hv
  have huv := SixQubit.Orbit7BoundaryPSD.overlap_zero_of_wedge_lower
    (uSpin c 0) (uSpin c 1) (vSpin d 0) (vSpin d 1) hu' hv' hsub
  have huC : uSpin c 0 * star (uSpin c 0) +
      uSpin c 1 * star (uSpin c 1) = (1/6 : ℂ) := by
    rw [show uSpin c 0 * star (uSpin c 0) +
        uSpin c 1 * star (uSpin c 1) = (uMass c : ℂ) by
      simpa [uSpin, uMass] using spinor_outer_trace c zero]
    rw [hu]
    norm_num
  have hvC : vSpin d 0 * star (vSpin d 0) +
      vSpin d 1 * star (vSpin d 1) = (1/6 : ℂ) := by
    rw [show vSpin d 0 * star (vSpin d 0) +
        vSpin d 1 * star (vSpin d 1) = (vMass d : ℂ) by
      simpa [vSpin, vMass] using spinor_outer_trace d activeAll]
    rw [hv]
    norm_num
  have haMass :
      (∑ e ∈ incidentPairs s,
        (spinor c (aBase e.1 e.2) 0 *
            star (spinor c (aBase e.1 e.2) 0) +
          spinor c (aBase e.1 e.2) 1 *
            star (spinor c (aBase e.1 e.2) 1))) = (1/3 : ℂ) := by
    calc
      _ = ∑ e ∈ incidentPairs s, (aMass c e.1 e.2 : ℂ) :=
        Finset.sum_congr rfl (fun e he => by
          simpa [aMass] using spinor_outer_trace c (aBase e.1 e.2))
      _ = (degreeA c s : ℂ) := by
        unfold degreeA
        push_cast
        rfl
      _ = 1/3 := by rw [(hdeg s).1]; norm_num
  have haOrth : ∀ e ∈ incidentPairs s,
      star (vSpin d 0) * spinor c (aBase e.1 e.2) 0 +
        star (vSpin d 1) * spinor c (aBase e.1 e.2) 1 = 0 := by
    intro e he
    simpa [xcoord, spinInner] using hxzero e he
  have hout := SixQubit.Orbit7BoundaryPSD.incident_outer_eq_two
    (incidentPairs s)
    (fun e => spinor c (aBase e.1 e.2) 0)
    (fun e => spinor c (aBase e.1 e.2) 1)
    (uSpin c 0) (uSpin c 1) (vSpin d 0) (vSpin d 1)
    huC hvC huv haMass haOrth
  have hA : ∀ i j, starA c s i j = 2 * U c i j := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [starA, AMat, U, block, outer, uSpin] using hout.1
    · simpa [starA, AMat, U, block, outer, uSpin] using hout.2.1
    · simpa [starA, AMat, U, block, outer, uSpin] using hout.2.2.1
    · simpa [starA, AMat, U, block, outer, uSpin] using hout.2.2.2
  refine ⟨s, hA, ?_⟩
  intro i j
  have hsId := star_identity c d hc hd hcode s i j
  have ha := hA i j
  linear_combination hsId - ha

/-- A full support mask is exactly nonvanishing of every canonical edge
coordinate. -/
theorem full_xcoord_support (c d : SS.State 6 ℂ)
    (hfull : SixQubit.Orbit7Mask.Full (supportMask (xcoord c d))) :
    ∀ e ∈ edgePairs, xcoord c d e ≠ 0 := by
  intro e he
  have hne : e.1 ≠ e.2 := by
    rcases e with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;> simp_all [edgePairs]
  exact (supportMask_adj (xcoord c d) e he).1 (hfull e.1 e.2 hne)

/-- Final gauge-free boundary dichotomy from arbitrary normalized uniform
full-fibre codewords and genuine distance-three KL: either a vertex star is
the rank-two-pair target, or every covariant edge coordinate is nonzero. -/
theorem boundary_reduction (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    TargetStar c d ∨
      ∀ e ∈ edgePairs, xcoord c d e ≠ 0 := by
  have hclass := support_classification c d hc hd hcode
  have hH := hafnians_zero c d hc hd hcode
  rcases hclass with hisol | hfull | hcenter | hsparse | hdense
  · exact Or.inl (isolated_target c d hc hd hnc hnd hcode hisol)
  · exact Or.inr (full_xcoord_support c d hfull)
  · exact (centered_impossible c d hc hd hnc hnd hcode hcenter).elim
  · exact (sparse_impossible (xcoord c d) hH hsparse).elim
  · exact (dense_impossible (xcoord c d) hH hdense).elim


end

end SixQubit.Orbit7Universal
