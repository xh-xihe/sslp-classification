import SixQubit.Orbit7PhysicalTangent

/-!
# Orbit 7: gauge-covariant two-spinor coordinates

These identities reconstruct a spinor from its inner products with an
anchor and its covariant perpendicular.  They are the exact bridge from the
physical `x,y,z` arrays to the phase-independent scalar algebra used in the
full-support endpoint argument.
-/

namespace SixQubit.Orbit7Universal

open scoped ComplexConjugate
open SixQubit SixQubit.Realize

noncomputable section

/-- Coordinates of the normalized `v` anchor in the covariant basis
`(u, u⊥)`.  The factor six compensates for the anchor mass `1/6`. -/
def anchorC (c d : SS.State 6 ℂ) : ℂ :=
  6 * spinInner (uSpin c) (vSpin d)

def anchorD (c d : SS.State 6 ℂ) : ℂ :=
  6 * spinInner (perpSpin (uSpin c)) (vSpin d)

/-- Division-free reconstruction in the orthogonal basis `(w,w⊥)`. -/
theorem reconstruct_spinor (w a : Spinor) (i : Fin 2) :
    (star (w 0) * w 0 + star (w 1) * w 1) * a i =
      spinInner w a * w i + spinInner (perpSpin w) a * perpSpin w i := by
  fin_cases i <;> simp [spinInner, perpSpin] <;> ring

private lemma u_mass_complex (c : SS.State 6 ℂ) (hu : uMass c = 1/6) :
    star (uSpin c 0) * uSpin c 0 + star (uSpin c 1) * uSpin c 1 =
      (1/6 : ℂ) := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) hu
  push_cast at h
  simpa [uMass, spinMass, uSpin, spinor, ← SixQubit.star_mul_self] using h

private lemma v_mass_complex (d : SS.State 6 ℂ) (hv : vMass d = 1/6) :
    star (vSpin d 0) * vSpin d 0 + star (vSpin d 1) * vSpin d 1 =
      (1/6 : ℂ) := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) hv
  push_cast at h
  simpa [vMass, spinMass, vSpin, spinor, ← SixQubit.star_mul_self] using h

/-- Exact anchor decomposition `v = C u + D u⊥`. -/
theorem anchor_decomposition (c d : SS.State 6 ℂ) (hu : uMass c = 1/6) :
    ∀ i, vSpin d i =
      anchorC c d * uSpin c i + anchorD c d * perpSpin (uSpin c) i := by
  intro i
  have h := reconstruct_spinor (uSpin c) (vSpin d) i
  rw [u_mass_complex c hu] at h
  unfold anchorC anchorD
  linear_combination 6 * h

/-- Perpendicular of the anchor decomposition, with all phase factors kept
explicit. -/
theorem perp_anchor_decomposition (c d : SS.State 6 ℂ)
    (hu : uMass c = 1/6) :
    ∀ i, perpSpin (vSpin d) i =
      -star (anchorD c d) * uSpin c i +
        star (anchorC c d) * perpSpin (uSpin c) i := by
  have hdec := anchor_decomposition c d hu
  intro i
  fin_cases i
  · have h := congrArg star (hdec 1)
    simp [perpSpin] at h ⊢
    linear_combination -h
  · have h := congrArg star (hdec 0)
    simp [perpSpin] at h ⊢
    linear_combination h

/-- The two covariant anchor coordinates form a unit vector. -/
theorem anchor_normSq (c d : SS.State 6 ℂ)
    (hu : uMass c = 1/6) (hv : vMass d = 1/6) :
    Complex.normSq (anchorC c d) + Complex.normSq (anchorD c d) = 1 := by
  have h := SixQubit.Spinor.lagrange
    (uSpin c 0) (uSpin c 1) (vSpin d 0) (vSpin d 1)
  have h' : Complex.normSq (spinInner (uSpin c) (vSpin d)) +
      Complex.normSq (spinInner (perpSpin (uSpin c)) (vSpin d)) =
        uMass c * vMass d := by
    rw [perp_inner]
    unfold spinInner
    rw [h]
    rfl
  rw [hu, hv] at h'
  unfold anchorC anchorD
  simp only [Complex.normSq_mul]
  norm_num
  linarith

/-- Complex polynomial spelling of `anchor_normSq`, ready for the covariant
projector-entry certificate. -/
theorem anchor_unit (c d : SS.State 6 ℂ)
    (hu : uMass c = 1/6) (hv : vMass d = 1/6) :
    anchorC c d * star (anchorC c d) +
      anchorD c d * star (anchorD c d) = 1 := by
  have h := congrArg (fun r : ℝ => (r : ℂ)) (anchor_normSq c d hu hv)
  push_cast at h
  simpa [← SixQubit.star_mul_self, mul_comm] using h

/-- Reconstruct an actual `a_e` spinor from its physical covariant
coordinates. -/
theorem acoord_reconstruction (c d : SS.State 6 ℂ)
    (hv : vMass d = 1/6) (e : Fin 5 × Fin 5) (i : Fin 2) :
    spinor c (aBase e.1 e.2) i =
      6 * (xcoord c d e * vSpin d i +
        ycoord c d e * perpSpin (vSpin d) i) := by
  have h := reconstruct_spinor (vSpin d)
    (spinor c (aBase e.1 e.2)) i
  rw [v_mass_complex d hv] at h
  change (1/6 : ℂ) * spinor c (aBase e.1 e.2) i =
    xcoord c d e * vSpin d i +
      ycoord c d e * perpSpin (vSpin d) i at h
  linear_combination 6 * h

/-- If `y_e=t x_e`, the actual `a_e` lies on the corresponding covariant
line. -/
theorem acoord_of_vertex_value (c d : SS.State 6 ℂ)
    (hv : vMass d = 1/6) (e : Fin 5 × Fin 5) (t : ℂ)
    (ht : ycoord c d e = t * xcoord c d e) (i : Fin 2) :
    spinor c (aBase e.1 e.2) i =
      6 * xcoord c d e *
        (vSpin d i + t * perpSpin (vSpin d) i) := by
  rw [acoord_reconstruction c d hv e i, ht]
  ring

/-- Reconstruct an actual `b_e` from pair-cross and the `z` coordinate. -/
theorem bcoord_reconstruction (c d : SS.State 6 ℂ)
    (hu : uMass c = 1/6) (e : Fin 5 × Fin 5)
    (hpair : spinInner (uSpin c) (spinor d (bBase e.1 e.2)) =
      -star (xcoord c d e)) (i : Fin 2) :
    spinor d (bBase e.1 e.2) i =
      6 * star (xcoord c d e) * (-uSpin c i) +
        6 * star (zcoord c d e) * perpSpin (uSpin c) i := by
  have h := reconstruct_spinor (uSpin c)
    (spinor d (bBase e.1 e.2)) i
  rw [u_mass_complex c hu, hpair] at h
  have hz : spinInner (perpSpin (uSpin c))
      (spinor d (bBase e.1 e.2)) = star (zcoord c d e) := by
    simp [zcoord]
  rw [hz] at h
  linear_combination 6 * h

/-- If `z_e=p x_e`, the actual `b_e` lies on its covariant line. -/
theorem bcoord_of_vertex_value (c d : SS.State 6 ℂ)
    (hu : uMass c = 1/6) (e : Fin 5 × Fin 5) (p : ℂ)
    (hpair : spinInner (uSpin c) (spinor d (bBase e.1 e.2)) =
      -star (xcoord c d e))
    (hp : zcoord c d e = p * xcoord c d e) (i : Fin 2) :
    spinor d (bBase e.1 e.2) i =
      6 * star (xcoord c d e) *
        (-uSpin c i + star p * perpSpin (uSpin c) i) := by
  rw [bcoord_reconstruction c d hu e hpair i, hp, star_mul]
  ring

end

end SixQubit.Orbit7Universal
