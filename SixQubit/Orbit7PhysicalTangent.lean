import SixQubit.Orbit7BoundaryIsolated
import SixQubit.Orbit7FullTangent

/-!
# Orbit 7: genuine KL rows produce the covariant tangent coordinates

The two auxiliary edge arrays are defined without choosing a spinor basis:

* `ycoord e = (v⊥)† a_e`,
* `zcoord e = conj ((u⊥)† b_e)`.

Projecting the actual zero `2 x 2` one-flip matrix onto the three pairs
`(u⊥,v)`, `(u,v⊥)`, and `(u⊥,v⊥)` gives the three polarized
hafnian systems.  No chart, rank, nonzero-spinor, or real-gauge hypothesis is
used in this file.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize

noncomputable section

/-- The manuscript's `y` coordinate, extracted from the `a` edge spinors. -/
def ycoord (c d : SS.State 6 ℂ) (e : Fin 5 × Fin 5) : ℂ :=
  spinInner (perpSpin (vSpin d)) (spinor c (aBase e.1 e.2))

/-- The manuscript's `z` coordinate, extracted from the `b` edge spinors. -/
def zcoord (c d : SS.State 6 ℂ) (e : Fin 5 × Fin 5) : ℂ :=
  star (spinInner (perpSpin (uSpin c)) (spinor d (bBase e.1 e.2)))

/-- Temporary local spelling of the polarized hafnian.  It is identified with
`PolarHafnian5` when the algebraic tangent module is imported below. -/
private def physicalPolarHafnian5 (x y : Fin 5 × Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![x (1,2) * y (3,4) + y (1,2) * x (3,4) +
      x (1,3) * y (2,4) + y (1,3) * x (2,4) +
      x (1,4) * y (2,3) + y (1,4) * x (2,3),
    x (0,2) * y (3,4) + y (0,2) * x (3,4) +
      x (0,3) * y (2,4) + y (0,3) * x (2,4) +
      x (0,4) * y (2,3) + y (0,4) * x (2,3),
    x (0,1) * y (3,4) + y (0,1) * x (3,4) +
      x (0,3) * y (1,4) + y (0,3) * x (1,4) +
      x (0,4) * y (1,3) + y (0,4) * x (1,3),
    x (0,1) * y (2,4) + y (0,1) * x (2,4) +
      x (0,2) * y (1,4) + y (0,2) * x (1,4) +
      x (0,4) * y (1,2) + y (0,4) * x (1,2),
    x (0,1) * y (2,3) + y (0,1) * x (2,3) +
      x (0,2) * y (1,3) + y (0,2) * x (1,3) +
      x (0,3) * y (1,2) + y (0,3) * x (1,2)]

private lemma physicalPolarHafnian5_comm
    (x y : Fin 5 × Fin 5 → ℂ) (v : Fin 5) :
    physicalPolarHafnian5 x y v = physicalPolarHafnian5 y x v := by
  fin_cases v <;> simp [physicalPolarHafnian5] <;> ring

private lemma physicalPolarHafnian5_neg_left
    (x y : Fin 5 × Fin 5 → ℂ) (v : Fin 5) :
    physicalPolarHafnian5 (fun e => -x e) y v =
      -physicalPolarHafnian5 x y v := by
  fin_cases v <;> simp [physicalPolarHafnian5] <;> ring

private lemma matEval_sum_physical (s t : Spinor)
    (E : Finset (Fin 5 × Fin 5)) (M : (Fin 5 × Fin 5) → Mat2) :
    matEval s (fun i j => ∑ e ∈ E, M e i j) t =
      ∑ e ∈ E, matEval s (M e) t := by
  classical
  simp [matEval, Finset.mul_sum, Finset.sum_mul, Finset.sum_comm]

private lemma matEval_cross_outer (s b a t : Spinor) :
    matEval s (fun i j => b i * star (a j)) t =
      spinInner s b * spinInner a t := by
  unfold matEval spinInner
  simp only [Fin.sum_univ_two]
  ring

private lemma matEval_oneFlip_physical (c d : SS.State 6 ℂ)
    (s t : Spinor) (v : Fin 5) :
    matEval s (oneFlipMat c d v) t =
      ∑ f ∈ nonincidentPairs v,
        spinInner s (spinor d (bBase f.1 f.2)) *
          spinInner (spinor c (SS.bxor (bBase f.1 f.2) (vmask v))) t := by
  unfold oneFlipMat
  rw [matEval_sum_physical]
  exact Finset.sum_congr rfl (fun f hf =>
    matEval_cross_outer s (spinor d (bBase f.1 f.2))
      (spinor c (SS.bxor (bBase f.1 f.2) (vmask v))) t)

private def nonincidentPhysical : Fin 5 → Finset (Fin 5 × Fin 5) :=
  ![{(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)},
    {(0,2),(0,3),(0,4),(2,3),(2,4),(3,4)},
    {(0,1),(0,3),(0,4),(1,3),(1,4),(3,4)},
    {(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)},
    {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}]

private theorem nonincidentPairs_physical : ∀ v,
    nonincidentPairs v = nonincidentPhysical v := by
  decide

/-- Generic projection identity.  The six oriented terms in a one-flip row
are exactly the six terms of the polarized hafnian. -/
private lemma projected_polar_expansion
    (c d : SS.State 6 ℂ) (s t : Spinor)
    (left right : Fin 5 × Fin 5 → ℂ)
    (hleft : ∀ e ∈ edgePairs,
      spinInner s (spinor d (bBase e.1 e.2)) = star (left e))
    (hright : ∀ e ∈ edgePairs,
      spinInner (spinor c (aBase e.1 e.2)) t = star (right e))
    (v : Fin 5) :
    matEval s (oneFlipMat c d v) t =
      star (physicalPolarHafnian5 left right v) := by
  rw [matEval_oneFlip_physical, nonincidentPairs_physical]
  fin_cases v
  · simp [nonincidentPhysical]
    rw [show SS.bxor (bBase 1 2) (vmask 0) = aBase 3 4 by decide,
      show SS.bxor (bBase 1 3) (vmask 0) = aBase 2 4 by decide,
      show SS.bxor (bBase 1 4) (vmask 0) = aBase 2 3 by decide,
      show SS.bxor (bBase 2 3) (vmask 0) = aBase 1 4 by decide,
      show SS.bxor (bBase 2 4) (vmask 0) = aBase 1 3 by decide,
      show SS.bxor (bBase 3 4) (vmask 0) = aBase 1 2 by decide]
    rw [hleft (1,2) (by decide), hleft (1,3) (by decide),
      hleft (1,4) (by decide), hleft (2,3) (by decide),
      hleft (2,4) (by decide), hleft (3,4) (by decide),
      hright (1,2) (by decide), hright (1,3) (by decide),
      hright (1,4) (by decide), hright (2,3) (by decide),
      hright (2,4) (by decide), hright (3,4) (by decide)]
    simp [physicalPolarHafnian5, map_add, map_mul]
    ring
  · simp [nonincidentPhysical]
    rw [show SS.bxor (bBase 0 2) (vmask 1) = aBase 3 4 by decide,
      show SS.bxor (bBase 0 3) (vmask 1) = aBase 2 4 by decide,
      show SS.bxor (bBase 0 4) (vmask 1) = aBase 2 3 by decide,
      show SS.bxor (bBase 2 3) (vmask 1) = aBase 0 4 by decide,
      show SS.bxor (bBase 2 4) (vmask 1) = aBase 0 3 by decide,
      show SS.bxor (bBase 3 4) (vmask 1) = aBase 0 2 by decide]
    rw [hleft (0,2) (by decide), hleft (0,3) (by decide),
      hleft (0,4) (by decide), hleft (2,3) (by decide),
      hleft (2,4) (by decide), hleft (3,4) (by decide),
      hright (0,2) (by decide), hright (0,3) (by decide),
      hright (0,4) (by decide), hright (2,3) (by decide),
      hright (2,4) (by decide), hright (3,4) (by decide)]
    simp [physicalPolarHafnian5, map_add, map_mul]
    ring
  · simp [nonincidentPhysical]
    rw [show SS.bxor (bBase 0 1) (vmask 2) = aBase 3 4 by decide,
      show SS.bxor (bBase 0 3) (vmask 2) = aBase 1 4 by decide,
      show SS.bxor (bBase 0 4) (vmask 2) = aBase 1 3 by decide,
      show SS.bxor (bBase 1 3) (vmask 2) = aBase 0 4 by decide,
      show SS.bxor (bBase 1 4) (vmask 2) = aBase 0 3 by decide,
      show SS.bxor (bBase 3 4) (vmask 2) = aBase 0 1 by decide]
    rw [hleft (0,1) (by decide), hleft (0,3) (by decide),
      hleft (0,4) (by decide), hleft (1,3) (by decide),
      hleft (1,4) (by decide), hleft (3,4) (by decide),
      hright (0,1) (by decide), hright (0,3) (by decide),
      hright (0,4) (by decide), hright (1,3) (by decide),
      hright (1,4) (by decide), hright (3,4) (by decide)]
    simp [physicalPolarHafnian5, map_add, map_mul]
    ring
  · simp [nonincidentPhysical]
    rw [show SS.bxor (bBase 0 1) (vmask 3) = aBase 2 4 by decide,
      show SS.bxor (bBase 0 2) (vmask 3) = aBase 1 4 by decide,
      show SS.bxor (bBase 0 4) (vmask 3) = aBase 1 2 by decide,
      show SS.bxor (bBase 1 2) (vmask 3) = aBase 0 4 by decide,
      show SS.bxor (bBase 1 4) (vmask 3) = aBase 0 2 by decide,
      show SS.bxor (bBase 2 4) (vmask 3) = aBase 0 1 by decide]
    rw [hleft (0,1) (by decide), hleft (0,2) (by decide),
      hleft (0,4) (by decide), hleft (1,2) (by decide),
      hleft (1,4) (by decide), hleft (2,4) (by decide),
      hright (0,1) (by decide), hright (0,2) (by decide),
      hright (0,4) (by decide), hright (1,2) (by decide),
      hright (1,4) (by decide), hright (2,4) (by decide)]
    simp [physicalPolarHafnian5, map_add, map_mul]
    ring
  · simp [nonincidentPhysical]
    rw [show SS.bxor (bBase 0 1) (vmask 4) = aBase 2 3 by decide,
      show SS.bxor (bBase 0 2) (vmask 4) = aBase 1 3 by decide,
      show SS.bxor (bBase 0 3) (vmask 4) = aBase 1 2 by decide,
      show SS.bxor (bBase 1 2) (vmask 4) = aBase 0 3 by decide,
      show SS.bxor (bBase 1 3) (vmask 4) = aBase 0 2 by decide,
      show SS.bxor (bBase 2 3) (vmask 4) = aBase 0 1 by decide]
    rw [hleft (0,1) (by decide), hleft (0,2) (by decide),
      hleft (0,3) (by decide), hleft (1,2) (by decide),
      hleft (1,3) (by decide), hleft (2,3) (by decide),
      hright (0,1) (by decide), hright (0,2) (by decide),
      hright (0,3) (by decide), hright (1,2) (by decide),
      hright (1,3) (by decide), hright (2,3) (by decide)]
    simp [physicalPolarHafnian5, map_add, map_mul]
    ring

private lemma matEval_zero_of_entries (s t : Spinor) (M : Mat2)
    (hM : ∀ i j, M i j = 0) : matEval s M t = 0 := by
  simp [matEval, hM]

private lemma a_inner_v (c d : SS.State 6 ℂ) (e : Fin 5 × Fin 5) :
    spinInner (spinor c (aBase e.1 e.2)) (vSpin d) =
      star (xcoord c d e) := by
  exact (star_spinInner (vSpin d) (spinor c (aBase e.1 e.2))).symm

private lemma a_inner_perp_v (c d : SS.State 6 ℂ) (e : Fin 5 × Fin 5) :
    spinInner (spinor c (aBase e.1 e.2)) (perpSpin (vSpin d)) =
      star (ycoord c d e) := by
  exact (star_spinInner (perpSpin (vSpin d))
    (spinor c (aBase e.1 e.2))).symm

private lemma perp_u_inner_b (c d : SS.State 6 ℂ) (e : Fin 5 × Fin 5) :
    spinInner (perpSpin (uSpin c)) (spinor d (bBase e.1 e.2)) =
      star (zcoord c d e) := by
  simp [zcoord]

/-- The three projected polarized hafnian systems are consequences of the
actual full-fibre KL equations. -/
private theorem physical_polar_equations_raw (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    (∀ v, physicalPolarHafnian5 (xcoord c d) (ycoord c d) v = 0) ∧
    (∀ v, physicalPolarHafnian5 (xcoord c d) (zcoord c d) v = 0) ∧
    (∀ v, physicalPolarHafnian5 (ycoord c d) (zcoord c d) v = 0) := by
  have hpair := paircross_projection c d hc hd hcode
  have hmat := oneflip_matrix c d hc hd hcode
  have hxy (v : Fin 5) :
      physicalPolarHafnian5 (xcoord c d) (ycoord c d) v = 0 := by
    have hz := matEval_zero_of_entries (uSpin c) (perpSpin (vSpin d))
      (oneFlipMat c d v) (hmat v)
    have he := projected_polar_expansion c d (uSpin c) (perpSpin (vSpin d))
      (fun e => -xcoord c d e) (ycoord c d)
      (fun e he => by simpa using hpair e he)
      (fun e he => a_inner_perp_v c d e) v
    rw [he] at hz
    have hs : star (physicalPolarHafnian5 (fun e => -xcoord c d e)
        (ycoord c d) v) = 0 := by
      exact hz
    have hp : physicalPolarHafnian5 (fun e => -xcoord c d e)
        (ycoord c d) v = 0 := by
      have := congrArg star hs
      simpa using this
    rw [physicalPolarHafnian5_neg_left] at hp
    exact neg_eq_zero.mp hp
  have hxz (v : Fin 5) :
      physicalPolarHafnian5 (xcoord c d) (zcoord c d) v = 0 := by
    have hz := matEval_zero_of_entries (perpSpin (uSpin c)) (vSpin d)
      (oneFlipMat c d v) (hmat v)
    have he := projected_polar_expansion c d (perpSpin (uSpin c)) (vSpin d)
      (zcoord c d) (xcoord c d)
      (fun e he => perp_u_inner_b c d e)
      (fun e he => a_inner_v c d e) v
    rw [he] at hz
    have hs : star (physicalPolarHafnian5 (zcoord c d) (xcoord c d) v) = 0 := by
      exact hz
    have hp : physicalPolarHafnian5 (zcoord c d) (xcoord c d) v = 0 := by
      have := congrArg star hs
      simpa using this
    rw [physicalPolarHafnian5_comm]
    exact hp
  have hyz (v : Fin 5) :
      physicalPolarHafnian5 (ycoord c d) (zcoord c d) v = 0 := by
    have hz := matEval_zero_of_entries (perpSpin (uSpin c))
      (perpSpin (vSpin d)) (oneFlipMat c d v) (hmat v)
    have he := projected_polar_expansion c d (perpSpin (uSpin c))
      (perpSpin (vSpin d)) (zcoord c d) (ycoord c d)
      (fun e he => perp_u_inner_b c d e)
      (fun e he => a_inner_perp_v c d e) v
    rw [he] at hz
    have hs : star (physicalPolarHafnian5 (zcoord c d) (ycoord c d) v) = 0 := by
      exact hz
    have hp : physicalPolarHafnian5 (zcoord c d) (ycoord c d) v = 0 := by
      have := congrArg star hs
      simpa using this
    rw [physicalPolarHafnian5_comm]
    exact hp
  exact ⟨hxy, hxz, hyz⟩

/-- The actual one-flip matrix supplies all three `PolarHafnian5` systems in
the exact spelling used by the algebraic tangent certificate. -/
theorem physical_polar_equations (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    (∀ v, PolarHafnian5 (xcoord c d) (ycoord c d) v = 0) ∧
    (∀ v, PolarHafnian5 (xcoord c d) (zcoord c d) v = 0) ∧
    (∀ v, PolarHafnian5 (ycoord c d) (zcoord c d) v = 0) := by
  rcases physical_polar_equations_raw c d hc hd hcode with
    ⟨hxy, hxz, hyz⟩
  constructor
  · intro v
    simpa [physicalPolarHafnian5, PolarHafnian5] using hxy v
  constructor
  · intro v
    simpa [physicalPolarHafnian5, PolarHafnian5] using hxz v
  · intro v
    simpa [physicalPolarHafnian5, PolarHafnian5] using hyz v

/-- The two auxiliary coordinates have equal squared modulus on every
canonical edge, as in the manuscript's parametrization.  This uses the
genuine scalar KL normal form and two-dimensional Lagrange identities; no
choice of normalized spinor basis is made. -/
theorem physical_coordinate_normSq_eq (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ e ∈ edgePairs,
      Complex.normSq (ycoord c d e) = Complex.normSq (zcoord c d e) := by
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, _hAt, _hBt, _hdeg, hedge⟩
  intro e he
  have hA0 := SixQubit.Spinor.lagrange
    (vSpin d 0) (vSpin d 1)
    (spinor c (aBase e.1 e.2) 0) (spinor c (aBase e.1 e.2) 1)
  have hinnerA :
      star (vSpin d 0) * spinor c (aBase e.1 e.2) 0 +
        star (vSpin d 1) * spinor c (aBase e.1 e.2) 1 =
          xcoord c d e := rfl
  have hdetA :
      vSpin d 0 * spinor c (aBase e.1 e.2) 1 -
        vSpin d 1 * spinor c (aBase e.1 e.2) 0 =
          ycoord c d e := by
    rw [ycoord, perp_inner]
  have hmassV :
      Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) =
        vMass d := rfl
  have hmassA :
      Complex.normSq (spinor c (aBase e.1 e.2) 0) +
        Complex.normSq (spinor c (aBase e.1 e.2) 1) =
          aMass c e.1 e.2 := rfl
  have hA :
      Complex.normSq (xcoord c d e) + Complex.normSq (ycoord c d e) =
        vMass d * aMass c e.1 e.2 := by
    rw [hinnerA, hdetA, hmassV, hmassA] at hA0
    exact hA0
  have hB0 := SixQubit.Spinor.lagrange
    (uSpin c 0) (uSpin c 1)
    (spinor d (bBase e.1 e.2) 0) (spinor d (bBase e.1 e.2) 1)
  have hzNorm :
      Complex.normSq (zcoord c d e) =
        Complex.normSq
          (uSpin c 0 * spinor d (bBase e.1 e.2) 1 -
            uSpin c 1 * spinor d (bBase e.1 e.2) 0) := by
    unfold zcoord
    rw [Complex.star_def, Complex.normSq_conj, perp_inner]
  have hBbase :
      Complex.normSq
          (spinInner (uSpin c) (spinor d (bBase e.1 e.2))) +
        Complex.normSq
          (uSpin c 0 * spinor d (bBase e.1 e.2) 1 -
            uSpin c 1 * spinor d (bBase e.1 e.2) 0) =
          uMass c * bMass d e.1 e.2 := by
    simpa [spinInner, uSpin, uMass, bMass, spinMass] using hB0
  have hBraw :
      Complex.normSq
          (spinInner (uSpin c) (spinor d (bBase e.1 e.2))) +
        Complex.normSq (zcoord c d e) =
          uMass c * bMass d e.1 e.2 := by
    rw [hzNorm]
    exact hBbase
  have hp := paircross_projection c d hc hd hcode e he
  have hB :
      Complex.normSq (xcoord c d e) + Complex.normSq (zcoord c d e) =
        uMass c * bMass d e.1 e.2 := by
    rw [hp] at hBraw
    simpa [Complex.star_def, Complex.normSq_neg, Complex.normSq_conj]
      using hBraw
  rw [hv] at hA
  rw [hu, ← hedge e he] at hB
  linarith

/-- On the full-support branch, the two auxiliary arrays constructed from the
actual code are vertex tangents of the actual base array.  The mixed auxiliary
polar system is retained as the third conclusion for the subsequent affine
and exceptional-vertex algebra. -/
theorem physical_vertex_tangents (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d)) :
    IsVertexTangent (xcoord c d) (ycoord c d) ∧
    IsVertexTangent (xcoord c d) (zcoord c d) ∧
    (∀ v, PolarHafnian5 (ycoord c d) (zcoord c d) v = 0) := by
  rcases physical_polar_equations c d hc hd hcode with ⟨hxy, hxz, hyz⟩
  have hH := hafnians_zero c d hc hd hcode
  exact ⟨full_hafnian_tangent_is_vertex (xcoord c d) (ycoord c d)
      hfull hH hxy,
    full_hafnian_tangent_is_vertex (xcoord c d) (zcoord c d)
      hfull hH hxz,
    hyz⟩

/-- Executable support-mask interface to `physical_vertex_tangents`.  The
only added input is precisely the full-support branch returned by the kernel
mask classifier. -/
theorem physical_vertex_tangents_of_full_mask (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : SixQubit.Orbit7Mask.Full (supportMask (xcoord c d))) :
    IsVertexTangent (xcoord c d) (ycoord c d) ∧
    IsVertexTangent (xcoord c d) (zcoord c d) ∧
    (∀ v, PolarHafnian5 (ycoord c d) (zcoord c d) v = 0) := by
  exact physical_vertex_tangents c d hc hd hcode
    (full_xcoord_support c d hfull)

/-- All gauge-covariant data needed by the remaining full-support algebra,
packaged without inserting any chart or rank premise. -/
structure PhysicalFullTangentData (c d : SS.State 6 ℂ) : Prop where
  y_vertex : IsVertexTangent (xcoord c d) (ycoord c d)
  z_vertex : IsVertexTangent (xcoord c d) (zcoord c d)
  yz_polar : ∀ v, PolarHafnian5 (ycoord c d) (zcoord c d) v = 0
  yz_norm : ∀ e ∈ edgePairs,
    Complex.normSq (ycoord c d e) = Complex.normSq (zcoord c d e)
  disjoint_edges : ∀ e ∈ edgePairs, ∀ f ∈ nonincidentBoth e,
    spinInner (spinor c (aBase e.1 e.2)) (spinor d (bBase f.1 f.2)) =
      spinInner (spinor c (aBase f.1 f.2)) (spinor d (bBase e.1 e.2))
  frameA : ∀ i j, sumA c i j = 2 * U c i j + 3 * W d i j
  frameB : ∀ i j, sumB d i j = 3 * U c i j + 2 * W d i j

/-- Strong physical bridge for the full-support branch.  Every field is
derived from the original full fibres, the two exact normalizations, genuine
distance three, and full support of `x`; none is an ansatz. -/
theorem physical_full_tangent_data (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d)) :
    PhysicalFullTangentData c d := by
  rcases physical_vertex_tangents c d hc hd hcode hfull with
    ⟨hy, hz, hyz⟩
  rcases global_frames c d hc hd hcode with ⟨hframeA, hframeB⟩
  exact {
    y_vertex := hy
    z_vertex := hz
    yz_polar := hyz
    yz_norm := physical_coordinate_normSq_eq c d hc hd hnc hnd hcode
    disjoint_edges := disjoint_relation c d hc hd hcode
    frameA := hframeA
    frameB := hframeB
  }

end

end SixQubit.Orbit7Universal
