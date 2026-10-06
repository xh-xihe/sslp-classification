import SixQubit.Orbit7UniversalMatrix
import SixQubit.Orbit7Mask
import SixQubit.Orbit7BoundaryAlgebra
import SixQubit.Orbit7BoundaryPSD
import SixQubit.Spinor

/-!
# Orbit 7 universal converse, IV: boundary-support bridge

The manuscript chooses a real basis for the two spinors `u,v`.  Here we avoid
that gauge choice altogether: the support coordinate is the covariant scalar
`x_e = v^dagger a_e`.  It differs from the normalized manuscript coordinate
by one fixed nonzero factor and therefore has the same support graph.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize

noncomputable section

set_option maxHeartbeats 4000000

def uSpin (c : SS.State 6 ℂ) : Spinor := spinor c zero
def vSpin (d : SS.State 6 ℂ) : Spinor := spinor d activeAll

/-- Gauge-covariant raw coordinate `x_e = v^dagger a_e`. -/
def xcoord (c d : SS.State 6 ℂ) (e : Fin 5 × Fin 5) : ℂ :=
  spinInner (vSpin d) (spinor c (aBase e.1 e.2))

/-- The rank-two-pair target in the raw matrix normalization:
`A_s = 2U` and `B_s = 2W`. -/
def TargetStar (c d : SS.State 6 ℂ) : Prop :=
  ∃ s, (∀ i j, starA c s i j = 2 * U c i j) ∧
    (∀ i j, starB d s i j = 2 * W d i j)

/-- The five four-vertex hafnians, in the vertex order `0,...,4`. -/
def Hafnian5 (x : Fin 5 × Fin 5 → ℂ) : Fin 5 → ℂ :=
  ![x (1,2) * x (3,4) + x (1,3) * x (2,4) + x (1,4) * x (2,3),
    x (0,2) * x (3,4) + x (0,3) * x (2,4) + x (0,4) * x (2,3),
    x (0,1) * x (3,4) + x (0,3) * x (1,4) + x (0,4) * x (1,3),
    x (0,1) * x (2,4) + x (0,2) * x (1,4) + x (0,4) * x (1,2),
    x (0,1) * x (2,3) + x (0,2) * x (1,3) + x (0,3) * x (1,2)]

/-- Conjugate symmetry of the two-component inner product. -/
lemma star_spinInner (s t : Spinor) : star (spinInner s t) = spinInner t s := by
  unfold spinInner
  simp
  ring

/-- The covariant form of `paircross`:
`u^dagger b_e = -conj(v^dagger a_e)`. -/
theorem paircross_projection (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ e ∈ edgePairs,
      spinInner (uSpin c) (spinor d (bBase e.1 e.2)) =
        -star (xcoord c d e) := by
  intro e he
  have hp := paircross c d hc hd hcode e he
  unfold uSpin xcoord vSpin
  rw [star_spinInner]
  linear_combination hp

def matEval (s : Spinor) (M : Mat2) (t : Spinor) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, star (s i) * M i j * t j

private lemma matEval_sum (s t : Spinor) (E : Finset (Fin 5 × Fin 5))
    (M : (Fin 5 × Fin 5) → Mat2) :
    matEval s (fun i j => ∑ e ∈ E, M e i j) t =
      ∑ e ∈ E, matEval s (M e) t := by
  classical
  simp [matEval, Finset.mul_sum, Finset.sum_mul, Finset.sum_comm]

private lemma matEval_outer' (s a b t : Spinor) :
    matEval s (fun i j => b i * star (a j)) t =
      spinInner s b * spinInner a t := by
  unfold matEval spinInner
  simp only [Fin.sum_univ_two]
  ring

private lemma matEval_oneFlip (c d : SS.State 6 ℂ) (v : Fin 5) :
    matEval (uSpin c) (oneFlipMat c d v) (vSpin d) =
      ∑ f ∈ nonincidentPairs v,
        spinInner (uSpin c) (spinor d (bBase f.1 f.2)) *
          spinInner (spinor c (SS.bxor (bBase f.1 f.2) (vmask v)))
            (vSpin d) := by
  unfold oneFlipMat
  rw [matEval_sum]
  exact Finset.sum_congr rfl (fun f hf =>
    matEval_outer' (uSpin c)
      (spinor c (SS.bxor (bBase f.1 f.2) (vmask v)))
      (spinor d (bBase f.1 f.2)) (vSpin d))

private lemma matEval_eq_zero (s t : Spinor) (M : Mat2)
    (hM : ∀ i j, M i j = 0) : matEval s M t = 0 := by
  simp [matEval, hM]

private def nonincidentExplicit : Fin 5 → Finset (Fin 5 × Fin 5) :=
  ![{(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)},
    {(0,2),(0,3),(0,4),(2,3),(2,4),(3,4)},
    {(0,1),(0,3),(0,4),(1,3),(1,4),(3,4)},
    {(0,1),(0,2),(0,4),(1,2),(1,4),(2,4)},
    {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}]

private theorem nonincidentPairs_explicit : ∀ v,
    nonincidentPairs v = nonincidentExplicit v := by
  decide

private lemma target_inner (c d : SS.State 6 ℂ) (e : Fin 5 × Fin 5) :
    spinInner (spinor c (aBase e.1 e.2)) (vSpin d) =
      star (xcoord c d e) := by
  unfold xcoord
  rw [star_spinInner]

private lemma target_inner_ij (c d : SS.State 6 ℂ) (i j : Fin 5) :
    spinInner (spinor c (aBase i j)) (vSpin d) =
      star (xcoord c d (i,j)) := target_inner c d (i,j)

private lemma oriented_hafnian_expansion (c d : SS.State 6 ℂ) (v : Fin 5) :
    (∑ f ∈ nonincidentPairs v,
      (-star (xcoord c d f)) *
        spinInner (spinor c (SS.bxor (bBase f.1 f.2) (vmask v))) (vSpin d)) =
      -2 * star (Hafnian5 (xcoord c d) v) := by
  rw [nonincidentPairs_explicit]
  fin_cases v
  · simp [nonincidentExplicit]
    rw [show SS.bxor (bBase 1 2) (vmask 0) = aBase 3 4 by decide,
      show SS.bxor (bBase 1 3) (vmask 0) = aBase 2 4 by decide,
      show SS.bxor (bBase 1 4) (vmask 0) = aBase 2 3 by decide,
      show SS.bxor (bBase 2 3) (vmask 0) = aBase 1 4 by decide,
      show SS.bxor (bBase 2 4) (vmask 0) = aBase 1 3 by decide,
      show SS.bxor (bBase 3 4) (vmask 0) = aBase 1 2 by decide]
    simp only [target_inner_ij]
    simp [Hafnian5]
    ring
  · simp [nonincidentExplicit]
    rw [show SS.bxor (bBase 0 2) (vmask 1) = aBase 3 4 by decide,
      show SS.bxor (bBase 0 3) (vmask 1) = aBase 2 4 by decide,
      show SS.bxor (bBase 0 4) (vmask 1) = aBase 2 3 by decide,
      show SS.bxor (bBase 2 3) (vmask 1) = aBase 0 4 by decide,
      show SS.bxor (bBase 2 4) (vmask 1) = aBase 0 3 by decide,
      show SS.bxor (bBase 3 4) (vmask 1) = aBase 0 2 by decide]
    simp only [target_inner_ij]
    simp [Hafnian5]
    ring
  · simp [nonincidentExplicit]
    rw [show SS.bxor (bBase 0 1) (vmask 2) = aBase 3 4 by decide,
      show SS.bxor (bBase 0 3) (vmask 2) = aBase 1 4 by decide,
      show SS.bxor (bBase 0 4) (vmask 2) = aBase 1 3 by decide,
      show SS.bxor (bBase 1 3) (vmask 2) = aBase 0 4 by decide,
      show SS.bxor (bBase 1 4) (vmask 2) = aBase 0 3 by decide,
      show SS.bxor (bBase 3 4) (vmask 2) = aBase 0 1 by decide]
    simp only [target_inner_ij]
    simp [Hafnian5]
    ring
  · simp [nonincidentExplicit]
    rw [show SS.bxor (bBase 0 1) (vmask 3) = aBase 2 4 by decide,
      show SS.bxor (bBase 0 2) (vmask 3) = aBase 1 4 by decide,
      show SS.bxor (bBase 0 4) (vmask 3) = aBase 1 2 by decide,
      show SS.bxor (bBase 1 2) (vmask 3) = aBase 0 4 by decide,
      show SS.bxor (bBase 1 4) (vmask 3) = aBase 0 2 by decide,
      show SS.bxor (bBase 2 4) (vmask 3) = aBase 0 1 by decide]
    simp only [target_inner_ij]
    simp [Hafnian5]
    ring
  · simp [nonincidentExplicit]
    rw [show SS.bxor (bBase 0 1) (vmask 4) = aBase 2 3 by decide,
      show SS.bxor (bBase 0 2) (vmask 4) = aBase 1 3 by decide,
      show SS.bxor (bBase 0 3) (vmask 4) = aBase 1 2 by decide,
      show SS.bxor (bBase 1 2) (vmask 4) = aBase 0 3 by decide,
      show SS.bxor (bBase 1 3) (vmask 4) = aBase 0 2 by decide,
      show SS.bxor (bBase 2 3) (vmask 4) = aBase 0 1 by decide]
    simp only [target_inner_ij]
    simp [Hafnian5]
    ring

/-- The five scalar hafnians follow from the genuine one-flip operator rows,
without a basis gauge or a division by `||v||`. -/
theorem hafnians_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ v, Hafnian5 (xcoord c d) v = 0 := by
  have hp := paircross_projection c d hc hd hcode
  have hm := oneflip_matrix c d hc hd hcode
  intro v
  have hz : matEval (uSpin c) (oneFlipMat c d v) (vSpin d) = 0 :=
    matEval_eq_zero _ _ _ (hm v)
  rw [matEval_oneFlip] at hz
  have hs :
      (∑ f ∈ nonincidentPairs v,
        spinInner (uSpin c) (spinor d (bBase f.1 f.2)) *
          spinInner (spinor c (SS.bxor (bBase f.1 f.2) (vmask v))) (vSpin d)) =
        ∑ f ∈ nonincidentPairs v,
          (-star (xcoord c d f)) *
            spinInner (spinor c (SS.bxor (bBase f.1 f.2) (vmask v)))
              (vSpin d) := by
    exact Finset.sum_congr rfl (fun f hf => by
      rw [hp f (nonincident_subset v hf)])
  rw [hs, oriented_hafnian_expansion] at hz
  have hstar : star (Hafnian5 (xcoord c d) v) = 0 := by
    linear_combination (-1 / 2 : ℂ) * hz
  have := congrArg star hstar
  simpa using this

/-! ## From scalar hafnians to the exhaustive support mask -/

private noncomputable def nz (z : ℂ) : Bool := if z = 0 then false else true

@[simp] private lemma nz_eq_true (z : ℂ) : nz z = true ↔ z ≠ 0 := by
  simp [nz]

@[simp] private lemma nz_mul (z w : ℂ) : nz (z * w) = (nz z && nz w) := by
  by_cases hz : z = 0 <;> by_cases hw : w = 0 <;> simp [nz, hz, hw]

private lemma good3_of_sum_zero (a b c : ℂ) (h : a + b + c = 0) :
    SixQubit.Orbit7Mask.good3 (nz a) (nz b) (nz c) = true := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0
  all_goals simp [SixQubit.Orbit7Mask.good3, nz, ha, hb, hc] at h ⊢

def supportMask (x : Fin 5 × Fin 5 → ℂ) : SixQubit.Orbit7Mask.Mask :=
  ⟨nz (x (0,1)), nz (x (0,2)), nz (x (0,3)), nz (x (0,4)),
    nz (x (1,2)), nz (x (1,3)), nz (x (1,4)),
    nz (x (2,3)), nz (x (2,4)), nz (x (3,4))⟩

/-- On canonical `K_5` edges, adjacency is exactly nonvanishing of `x`. -/
lemma supportMask_adj (x : Fin 5 × Fin 5 → ℂ) : ∀ e ∈ edgePairs,
    SixQubit.Orbit7Mask.Adj (supportMask x) e.1 e.2 ↔ x e ≠ 0 := by
  rintro ⟨i,j⟩ he
  fin_cases i <;> fin_cases j <;>
    simp_all [edgePairs, supportMask, SixQubit.Orbit7Mask.Adj,
      SixQubit.Orbit7Mask.edge]

/-- A vanishing hafnian on each four-set makes the support mask admissible. -/
theorem supportMask_admissible (x : Fin 5 × Fin 5 → ℂ)
    (hH : ∀ v, Hafnian5 x v = 0) :
    SixQubit.Orbit7Mask.AdmissibleB (supportMask x) = true := by
  have h0 := good3_of_sum_zero
    (x (1,2) * x (3,4)) (x (1,3) * x (2,4)) (x (1,4) * x (2,3))
    (by simpa [Hafnian5] using hH 0)
  have h1 := good3_of_sum_zero
    (x (0,2) * x (3,4)) (x (0,3) * x (2,4)) (x (0,4) * x (2,3))
    (by simpa [Hafnian5] using hH 1)
  have h2 := good3_of_sum_zero
    (x (0,1) * x (3,4)) (x (0,3) * x (1,4)) (x (0,4) * x (1,3))
    (by simpa [Hafnian5] using hH 2)
  have h3 := good3_of_sum_zero
    (x (0,1) * x (2,4)) (x (0,2) * x (1,4)) (x (0,4) * x (1,2))
    (by simpa [Hafnian5] using hH 3)
  have h4 := good3_of_sum_zero
    (x (0,1) * x (2,3)) (x (0,2) * x (1,3)) (x (0,3) * x (1,2))
    (by simpa [Hafnian5] using hH 4)
  simpa [SixQubit.Orbit7Mask.AdmissibleB, supportMask, nz_mul] using
    And.intro (And.intro (And.intro (And.intro h0 h1) h2) h3) h4

/-- The exact five-way support classification reached from genuine KL. -/
theorem support_classification (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    let g := supportMask (xcoord c d)
    SixQubit.Orbit7Mask.Isolated g ∨ SixQubit.Orbit7Mask.Full g ∨
      SixQubit.Orbit7Mask.Centered g ∨ SixQubit.Orbit7Mask.SparsePattern g ∨
      SixQubit.Orbit7Mask.DensePattern g := by
  let x := xcoord c d
  let g := supportMask x
  have hH : ∀ v, Hafnian5 x v = 0 := hafnians_zero c d hc hd hcode
  exact SixQubit.Orbit7Mask.classify g (supportMask_admissible x hH)

/-! ## Covariant norm estimates -/

private lemma matEval_block (s : Spinor) (f : SS.State 6 ℂ)
    (y : SS.BitString 6) :
    matEval s (block f y) s =
      (Complex.normSq (spinInner s (spinor f y)) : ℂ) := by
  rw [show block f y = fun i j => spinor f y i * star (spinor f y j) by rfl,
    matEval_outer', ← star_spinInner s (spinor f y)]
  rw [mul_comm, SixQubit.star_mul_self]

private lemma spinInner_self (f : SS.State 6 ℂ) (y : SS.BitString 6) :
    spinInner (spinor f y) (spinor f y) = (spinMass f y : ℂ) := by
  unfold spinInner spinor spinMass
  rw [SixQubit.star_mul_self, SixQubit.star_mul_self]
  push_cast
  rfl

private lemma matEval_sumA_v (c d : SS.State 6 ℂ) :
    matEval (vSpin d) (sumA c) (vSpin d) =
      ((∑ e ∈ edgePairs, Complex.normSq (xcoord c d e) : ℝ) : ℂ) := by
  unfold sumA AMat
  rw [matEval_sum]
  push_cast
  exact Finset.sum_congr rfl (fun e he => by
    rw [matEval_block]
    rfl)

private lemma matEval_linear (s : Spinor) (M N : Mat2) (a b : ℂ) :
    matEval s (fun i j => a * M i j + b * N i j) s =
      a * matEval s M s + b * matEval s N s := by
  unfold matEval
  simp only [Fin.sum_univ_two]
  ring

/-- Exact covariant frame expectation. -/
theorem xcoord_total (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    (∑ e ∈ edgePairs, Complex.normSq (xcoord c d e)) =
      2 * Complex.normSq (spinInner (vSpin d) (uSpin c)) +
        3 * (vMass d)^2 := by
  have hf := (global_frames c d hc hd hcode).1
  have hmat :
      matEval (vSpin d) (sumA c) (vSpin d) =
        matEval (vSpin d)
          (fun i j => 2 * U c i j + 3 * W d i j) (vSpin d) := by
    apply congrArg (fun M : Mat2 => matEval (vSpin d) M (vSpin d))
    funext i j
    exact hf i j
  rw [matEval_sumA_v, matEval_linear] at hmat
  unfold U W at hmat
  rw [matEval_block, matEval_block] at hmat
  unfold vSpin at hmat
  unfold uSpin vSpin
  rw [spinInner_self] at hmat
  have hcast :
      (((∑ e ∈ edgePairs, Complex.normSq (xcoord c d e)) : ℝ) : ℂ) =
        ((2 * Complex.normSq (spinInner (spinor d activeAll) (spinor c zero)) +
          3 * (vMass d)^2 : ℝ) : ℂ) := by
    push_cast
    simpa [Complex.normSq_ofReal, vMass, pow_two] using hmat
  exact_mod_cast hcast

/-- Cauchy--Schwarz with the exact rigid norm `||v||^2=1/6`. -/
theorem xcoord_edge_bound (c d : SS.State 6 ℂ) (hv : vMass d = 1/6) :
    ∀ e, Complex.normSq (xcoord c d e) ≤ (1/6) * aMass c e.1 e.2 := by
  intro e
  have hL := SixQubit.Spinor.lagrange
    (vSpin d 0) (vSpin d 1)
    (spinor c (aBase e.1 e.2) 0) (spinor c (aBase e.1 e.2) 1)
  have hn := Complex.normSq_nonneg
    (vSpin d 0 * spinor c (aBase e.1 e.2) 1 -
      vSpin d 1 * spinor c (aBase e.1 e.2) 0)
  unfold vSpin spinor at hL
  unfold vSpin spinor at hn
  unfold xcoord spinInner vSpin spinor aMass spinMass
  change Complex.normSq (d activeAll) +
      Complex.normSq (d (SS.bxor activeAll abit)) = 1/6 at hv
  simp at hL hn ⊢
  rw [SS.bxor_comm activeAll abit] at hv
  rw [hv] at hL
  norm_num at hL ⊢
  linarith

/-- A proper support contained in one star is impossible: the covariant
`x`-mass is at least `1/12`, while Cauchy--Schwarz and the physical star mass
bound it by `(1/6)(1/3)=1/18`. -/
theorem centered_impossible (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ¬ SixQubit.Orbit7Mask.Centered (supportMask (xcoord c d)) := by
  intro hcenter
  rcases hcenter with ⟨s, hs⟩
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, hAt, hBt, hdeg, hedge⟩
  have htotal := xcoord_total c d hc hd hcode
  have hlarge : (1/12 : ℝ) ≤
      ∑ e ∈ edgePairs, Complex.normSq (xcoord c d e) := by
    rw [htotal, hv]
    have hn := Complex.normSq_nonneg (spinInner (vSpin d) (uSpin c))
    norm_num
    linarith
  have hzero : ∀ e ∈ edgePairs, e ∉ incidentPairs s → xcoord c d e = 0 := by
    intro e he hnot
    by_contra hx
    have ha : SixQubit.Orbit7Mask.Adj (supportMask (xcoord c d)) e.1 e.2 :=
      (supportMask_adj (xcoord c d) e he).2 hx
    have hor := hs e.1 e.2 ha
    have hnmem : e.1 ≠ s ∧ e.2 ≠ s := by
      simpa [incidentPairs, he] using hnot
    exact hor.elim hnmem.1 hnmem.2
  have heq :
      (∑ e ∈ edgePairs, Complex.normSq (xcoord c d e)) =
        ∑ e ∈ incidentPairs s, Complex.normSq (xcoord c d e) := by
    symm
    apply Finset.sum_subset (incident_subset s)
    intro e he hnot
    rw [hzero e he hnot, Complex.normSq_zero]
  have hle := xcoord_edge_bound c d hv
  have hsum :
      (∑ e ∈ incidentPairs s, Complex.normSq (xcoord c d e)) ≤
        (1/6) * degreeA c s := by
    unfold degreeA
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e he => hle e)
  rw [(hdeg s).1] at hsum
  rw [heq] at hlarge
  norm_num at hsum
  linarith

/-! ## Permutation-free access to the five hafnian equations -/

def canonEdge (i j : Fin 5) : Fin 5 × Fin 5 :=
  if i < j then (i,j) else (j,i)

def xEdge (x : Fin 5 × Fin 5 → ℂ) (i j : Fin 5) : ℂ := x (canonEdge i j)

lemma xEdge_comm (x : Fin 5 × Fin 5 → ℂ) (i j : Fin 5) :
    xEdge x i j = xEdge x j i := by
  unfold xEdge canonEdge
  by_cases hij : i < j
  · have hji : ¬ j < i := by omega
    simp [hij, hji]
  · by_cases hji : j < i
    · simp [hij, hji]
    · have h : i = j := by omega
      simp [h]

lemma supportMask_adj_edge (x : Fin 5 × Fin 5 → ℂ) (i j : Fin 5)
    (hij : i ≠ j) :
    SixQubit.Orbit7Mask.Adj (supportMask x) i j ↔ xEdge x i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;>
    simp_all [supportMask, SixQubit.Orbit7Mask.Adj, SixQubit.Orbit7Mask.edge,
      xEdge, canonEdge]

/-- Any ordering of five distinct vertices reads one of the five stored
hafnian equations. -/
private theorem hafnian_distinct (x : Fin 5 × Fin 5 → ℂ)
    (hH : ∀ v, Hafnian5 x v = 0) :
    ∀ a b c d e, SixQubit.Orbit7Mask.FiveDistinct a b c d e →
      xEdge x a b * xEdge x c d + xEdge x a c * xEdge x b d +
        xEdge x a d * xEdge x b c = 0 := by
  have h0 := hH 0
  have h1 := hH 1
  have h2 := hH 2
  have h3 := hH 3
  have h4 := hH 4
  simp [Hafnian5] at h0 h1 h2 h3 h4
  intro a b c d e hdistinct
  unfold SixQubit.Orbit7Mask.FiveDistinct at hdistinct
  fin_cases a <;> fin_cases b <;> simp_all
  all_goals fin_cases c <;> simp_all
  all_goals fin_cases d <;> simp_all
  all_goals fin_cases e <;>
    simp_all [xEdge, canonEdge]
  all_goals ring_nf at h0 h1 h2 h3 h4 ⊢
  all_goals assumption

theorem sparse_impossible (x : Fin 5 × Fin 5 → ℂ)
    (hH : ∀ v, Hafnian5 x v = 0) :
    ¬ SixQubit.Orbit7Mask.SparsePattern (supportMask x) := by
  rintro ⟨a,b,c,d,e,hdist,hac,had,hae,hbc,hbd,hbe,hncd,hnce,hnde⟩
  have h_ac : a ≠ c := by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist; tauto
  have h_ad : a ≠ d := by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist; tauto
  have h_ae : a ≠ e := by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist; tauto
  have h_bc : b ≠ c := by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist; tauto
  have h_bd : b ≠ d := by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist; tauto
  have h_be : b ≠ e := by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist; tauto
  have h_cd : c ≠ d := by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist; tauto
  have h_ce : c ≠ e := by
    unfold SixQubit.Orbit7Mask.FiveDistinct at hdist
    tauto
  have h_de : d ≠ e := by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist; tauto
  have nz_ac := (supportMask_adj_edge x a c h_ac).mp hac
  have nz_ad := (supportMask_adj_edge x a d h_ad).mp had
  have nz_ae := (supportMask_adj_edge x a e h_ae).mp hae
  have nz_bc := (supportMask_adj_edge x b c h_bc).mp hbc
  have nz_bd := (supportMask_adj_edge x b d h_bd).mp hbd
  have nz_be := (supportMask_adj_edge x b e h_be).mp hbe
  have z_cd : xEdge x c d = 0 := by
    by_contra h
    exact hncd ((supportMask_adj_edge x c d h_cd).mpr h)
  have z_ce : xEdge x c e = 0 := by
    by_contra h
    exact hnce ((supportMask_adj_edge x c e h_ce).mpr h)
  have z_de : xEdge x d e = 0 := by
    by_contra h
    exact hnde ((supportMask_adj_edge x d e h_de).mpr h)
  have q1 := hafnian_distinct x hH a d b e c
    (by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist ⊢; tauto)
  have q2 := hafnian_distinct x hH a c b e d
    (by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist ⊢; tauto)
  have q3 := hafnian_distinct x hH a c b d e
    (by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist ⊢; tauto)
  rw [z_de, xEdge_comm x d b] at q1
  rw [z_ce, xEdge_comm x c b] at q2
  rw [z_cd, xEdge_comm x c b] at q3
  simp at q1 q2 q3
  exact SixQubit.Orbit7BoundaryAlgebra.three_two_term_contradiction
    (xEdge x a d) (xEdge x a e) (xEdge x b d)
    (xEdge x b e) (xEdge x a c) (xEdge x b c)
    nz_ad nz_be nz_bc q1 q2 q3

theorem dense_impossible (x : Fin 5 × Fin 5 → ℂ)
    (hH : ∀ v, Hafnian5 x v = 0) :
    ¬ SixQubit.Orbit7Mask.DensePattern (supportMask x) := by
  rintro ⟨a,b,c,d,e,hdist,hnde,had,hae,hbd,hbe,hcd,hce⟩
  have h_ad : a ≠ d := by
    unfold SixQubit.Orbit7Mask.FiveDistinct at hdist
    tauto
  have h_ae : a ≠ e := by
    unfold SixQubit.Orbit7Mask.FiveDistinct at hdist
    tauto
  have h_bd : b ≠ d := by
    unfold SixQubit.Orbit7Mask.FiveDistinct at hdist
    tauto
  have h_be : b ≠ e := by
    unfold SixQubit.Orbit7Mask.FiveDistinct at hdist
    tauto
  have h_cd : c ≠ d := by
    unfold SixQubit.Orbit7Mask.FiveDistinct at hdist
    tauto
  have h_ce : c ≠ e := by
    unfold SixQubit.Orbit7Mask.FiveDistinct at hdist
    tauto
  have h_de : d ≠ e := by
    unfold SixQubit.Orbit7Mask.FiveDistinct at hdist
    tauto
  have nz_ad := (supportMask_adj_edge x a d h_ad).mp had
  have nz_ae := (supportMask_adj_edge x a e h_ae).mp hae
  have nz_bd := (supportMask_adj_edge x b d h_bd).mp hbd
  have nz_be := (supportMask_adj_edge x b e h_be).mp hbe
  have nz_cd := (supportMask_adj_edge x c d h_cd).mp hcd
  have nz_ce := (supportMask_adj_edge x c e h_ce).mp hce
  have z_de : xEdge x d e = 0 := by
    by_contra h
    exact hnde ((supportMask_adj_edge x d e h_de).mpr h)
  have q1 := hafnian_distinct x hH b d c e a
    (by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist ⊢; tauto)
  have q2 := hafnian_distinct x hH a d c e b
    (by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist ⊢; tauto)
  have q3 := hafnian_distinct x hH a d b e c
    (by unfold SixQubit.Orbit7Mask.FiveDistinct at hdist ⊢; tauto)
  rw [z_de, xEdge_comm x d c] at q1
  rw [z_de, xEdge_comm x d c] at q2
  rw [z_de, xEdge_comm x d b] at q3
  simp at q1 q2 q3
  have q1' : xEdge x b d * xEdge x c e +
      xEdge x c d * xEdge x b e = 0 := by
    linear_combination q1
  have q2' : xEdge x a d * xEdge x c e +
      xEdge x c d * xEdge x a e = 0 := by
    linear_combination q2
  have q3' : xEdge x a d * xEdge x b e +
      xEdge x b d * xEdge x a e = 0 := by
    linear_combination q3
  exact SixQubit.Orbit7BoundaryAlgebra.three_two_term_contradiction
    (xEdge x b d) (xEdge x c d) (xEdge x b e)
    (xEdge x c e) (xEdge x a d) (xEdge x a e)
    nz_bd nz_ce nz_ae q1' q2' q3'

end

end SixQubit.Orbit7Universal
