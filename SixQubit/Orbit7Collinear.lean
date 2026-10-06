import SixQubit.Orbit7TargetEnumerator
import SixQubit.Orbit7BoundaryIsolated
import SixQubit.Orbit7CovariantAlgebra
import SixQubit.Orbit7PairRank

/-!
# Orbit 7: the collinear endpoint

This module treats the endpoint at which the two extreme spinors are
collinear.  The proof stays in the original uniform fibre coordinates.  In
particular, it expands three genuine weight-one Pauli traces and proves their
total squared modulus is four; no abstract purity-to-enumerator implication is
used.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize SS.MacWilliams

noncomputable section

set_option maxRecDepth 10000

/-! ## Division-free spinor algebra -/

/-- The squared length of the sum of two Bloch vectors is the square of the
total spinor mass, minus four times the squared determinant.  This is the
rank-two purity identity in completely expanded, division-free form. -/
theorem bloch_add_sq_eq_mass_sq_sub_wedge
    (a₀ a₁ b₀ b₁ : ℂ) :
    Complex.normSq
        (SixQubit.Orbit7Spinor.bx a₀ a₁ +
          SixQubit.Orbit7Spinor.bx b₀ b₁) +
      Complex.normSq
        (SixQubit.Orbit7Spinor.by' a₀ a₁ +
          SixQubit.Orbit7Spinor.by' b₀ b₁) +
      Complex.normSq
        (SixQubit.Orbit7Spinor.bz a₀ a₁ +
          SixQubit.Orbit7Spinor.bz b₀ b₁) =
      (Complex.normSq a₀ + Complex.normSq a₁ +
        Complex.normSq b₀ + Complex.normSq b₁) ^ 2 -
        4 * Complex.normSq (a₀ * b₁ - a₁ * b₀) := by
  norm_num [SixQubit.Orbit7Spinor.bx, SixQubit.Orbit7Spinor.by',
    SixQubit.Orbit7Spinor.bz, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.star_def]
  ring

/-! ## The three actual Pauli rows on the zero-angle coordinate

The reduced-matrix implementation keeps its finite block decomposition
private.  We repeat only the three one-qubit rows needed here, so that the
endpoint certificate depends on actual `diagOn` and `trProj` expressions.
-/

private theorem col_S0_blocks : S0 = spinSupport zero ∪ aShellSupport := by
  decide

private theorem col_S0_blocks_disjoint :
    Disjoint (spinSupport zero) aShellSupport := by
  decide

private lemma col_sum_aShell (F : SS.BitString 6 → ℂ) :
    (∑ x ∈ aShellSupport, F x) =
      ∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2), F x := by
  unfold aShellSupport
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact aShell_disjoint e he f hf hef)]

private lemma col_sum_S0_blocks (F : SS.BitString 6 → ℂ) :
    (∑ x ∈ S0, F x) =
      (∑ x ∈ spinSupport zero, F x) +
        ∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2), F x := by
  rw [col_S0_blocks, Finset.sum_union col_S0_blocks_disjoint,
    col_sum_aShell]

private theorem col_zero_eq_zeroMask :
    zero = (fun _ ↦ false) := by
  decide

private theorem col_abit_eq_basis :
    abit = SS.stdBasis (0 : Fin 6) := by
  decide

private theorem col_bdot_false : ∀ x : SS.BitString 6,
    SS.bdot (fun _ ↦ false) x = false := by
  decide

private lemma col_flip_flip' (y : SS.BitString 6) :
    SS.bxor abit (SS.bxor y abit) = y := by
  rw [SS.bxor_comm abit, SS.bxor_bxor_cancel]

private theorem col_S0_closed_zero :
    S0.filter (fun x ↦ SS.bxor x zero ∈ S0) = S0 := by
  decide

private theorem col_S0_closed_abit :
    S0.filter (fun x ↦ SS.bxor x abit ∈ S0) = S0 := by
  decide

private theorem col_base_bit_zero :
    zero 0 = false ∧
      (∀ e ∈ edgePairs, aBase e.1 e.2 0 = false) := by
  decide

private lemma col_bdot_abit_base (y : SS.BitString 6)
    (hy : y 0 = false) :
    SS.bdot abit y = false := by
  rw [col_abit_eq_basis, bdot_stdBasis, hy]

private lemma col_bdot_abit_flip (y : SS.BitString 6)
    (hy : y 0 = false) :
    SS.bdot abit (SS.bxor y abit) = true := by
  rw [col_abit_eq_basis, bdot_stdBasis]
  simp [SS.bxor, SS.stdBasis, hy]

private lemma col_block_Z (f : SS.State 6 ℂ) (y : SS.BitString 6)
    (hy : y 0 = false) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot abit x) (star (f (SS.bxor x zero)) * f x)) =
      block f y 0 0 - block f y 1 1 := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  have h0 := col_bdot_abit_base y hy
  have h1 := col_bdot_abit_flip y hy
  simp [spinSupport, block, outer, spinor, col_zero_eq_zeroMask, hne,
    h0, h1]
  ring

private lemma col_block_X (f : SS.State 6 ℂ) (y : SS.BitString 6) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot zero x) (star (f (SS.bxor x abit)) * f x)) =
      block f y 0 1 + block f y 1 0 := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  simp [spinSupport, block, outer, spinor, col_zero_eq_zeroMask, hne,
    col_bdot_false, col_flip_flip']
  ring

private lemma col_block_XZ (f : SS.State 6 ℂ) (y : SS.BitString 6)
    (hy : y 0 = false) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot abit x) (star (f (SS.bxor x abit)) * f x)) =
      block f y 0 1 - block f y 1 0 := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  have h0 := col_bdot_abit_base y hy
  have h1 := col_bdot_abit_flip y hy
  simp [spinSupport, block, outer, spinor, hne, h0, h1,
    col_flip_flip']
  ring

private lemma col_diag_Z_c (c : SS.State 6 ℂ) :
    diagOn S0 c zero abit = rhoC c 0 0 - rhoC c 1 1 := by
  unfold diagOn
  rw [col_S0_closed_zero, col_sum_S0_blocks,
    col_block_Z c zero col_base_bit_zero.1]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2),
        signMul (SS.bdot abit x) (star (c (SS.bxor x zero)) * c x)) =
      ∑ e ∈ edgePairs,
        (block c (aBase e.1 e.2) 0 0 -
          block c (aBase e.1 e.2) 1 1) := by
    exact Finset.sum_congr rfl (fun e he =>
      col_block_Z c (aBase e.1 e.2) (col_base_bit_zero.2 e he))
  rw [hs, Finset.sum_sub_distrib]
  unfold rhoC U sumA AMat
  ring

private lemma col_diag_X_c (c : SS.State 6 ℂ) :
    diagOn S0 c abit zero = rhoC c 0 1 + rhoC c 1 0 := by
  unfold diagOn
  rw [col_S0_closed_abit, col_sum_S0_blocks, col_block_X]
  simp_rw [col_block_X]
  rw [Finset.sum_add_distrib]
  unfold rhoC U sumA AMat
  ring

private lemma col_diag_XZ_c (c : SS.State 6 ℂ) :
    diagOn S0 c abit abit = rhoC c 0 1 - rhoC c 1 0 := by
  unfold diagOn
  rw [col_S0_closed_abit, col_sum_S0_blocks,
    col_block_XZ c zero col_base_bit_zero.1]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2),
        signMul (SS.bdot abit x) (star (c (SS.bxor x abit)) * c x)) =
      ∑ e ∈ edgePairs,
        (block c (aBase e.1 e.2) 0 1 -
          block c (aBase e.1 e.2) 1 0) := by
    exact Finset.sum_congr rfl (fun e he =>
      col_block_XZ c (aBase e.1 e.2) (col_base_bit_zero.2 e he))
  rw [hs, Finset.sum_sub_distrib]
  unfold rhoC U sumA AMat
  ring

@[simp] private theorem col_tPX_numY : tPX.numY = 0 := by decide
@[simp] private theorem col_tPY_numY : tPY.numY = 1 := by decide
@[simp] private theorem col_tPZ_numY : tPZ.numY = 0 := by decide

@[simp] private theorem col_tPX_wt : tPX.wt = 1 := by decide
@[simp] private theorem col_tPY_wt : tPY.wt = 1 := by decide
@[simp] private theorem col_tPZ_wt : tPZ.wt = 1 := by decide

/-- A genuine projector trace is twice the first fibre's diagonal support
sum.  Both the support conversion and equality of the two logical diagonal
entries are consequences of the supplied full fibres and `HasDistance`. -/
private lemma col_trProj_eq_two_diagOn (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    trProj ![c,d] P =
      2 * (Complex.I ^ P.numY * diagOn S0 c P.x P.z) := by
  rw [trProj, Fin.sum_univ_two]
  change SS.innerC c (SS.pauliAct P c) +
      SS.innerC d (SS.pauliAct P d) = _
  rw [innerC_eq_diagOn S0 c (full_support0 hc) P,
    innerC_eq_diagOn S2 d (full_support2 hd) P,
    ← diagOn_eq_of_hasDistance S0 S2 c d (full_support0 hc)
      (full_support2 hd) hcode P.x P.z hw]
  ring

/-- The three genuine weight-one Pauli traces on the zero-angle qubit,
expanded all the way to the two extreme spinors.  No collinearity is used in
this row-extraction theorem. -/
theorem zero_angle_trace_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    trProj ![c,d] tPX = 6 *
        (SixQubit.Orbit7Spinor.bx (uSpin c 0) (uSpin c 1) +
          SixQubit.Orbit7Spinor.bx (vSpin d 0) (vSpin d 1)) ∧
    trProj ![c,d] tPY = -6 *
        (SixQubit.Orbit7Spinor.by' (uSpin c 0) (uSpin c 1) +
          SixQubit.Orbit7Spinor.by' (vSpin d 0) (vSpin d 1)) ∧
    trProj ![c,d] tPZ = 6 *
        (SixQubit.Orbit7Spinor.bz (uSpin c 0) (uSpin c 1) +
          SixQubit.Orbit7Spinor.bz (vSpin d 0) (vSpin d 1)) := by
  have hr := rho_identity c d hc hd hcode
  have hX := col_trProj_eq_two_diagOn c d hc hd hcode tPX (by decide)
  have hY := col_trProj_eq_two_diagOn c d hc hd hcode tPY (by decide)
  have hZ := col_trProj_eq_two_diagOn c d hc hd hcode tPZ (by decide)
  change trProj ![c,d] tPX =
    2 * (Complex.I ^ tPX.numY * diagOn S0 c abit zero) at hX
  change trProj ![c,d] tPY =
    2 * (Complex.I ^ tPY.numY * diagOn S0 c abit abit) at hY
  change trProj ![c,d] tPZ =
    2 * (Complex.I ^ tPZ.numY * diagOn S0 c zero abit) at hZ
  rw [col_diag_X_c, hr 0 1, hr 1 0] at hX
  rw [col_diag_XZ_c, hr 0 1, hr 1 0] at hY
  rw [col_diag_Z_c, hr 0 0, hr 1 1] at hZ
  simp only [col_tPX_numY, col_tPY_numY, col_tPZ_numY, pow_zero,
    pow_one, one_mul] at hX hY hZ
  have expand : ∀ (i j : Fin 2),
      U c i j = uSpin c i * star (uSpin c j) ∧
      W d i j = vSpin d i * star (vSpin d j) := by
    intro i j
    exact ⟨rfl, rfl⟩
  simp only [expand] at hX hY hZ
  unfold SixQubit.Orbit7Spinor.bx SixQubit.Orbit7Spinor.by'
    SixQubit.Orbit7Spinor.bz
  constructor
  · linear_combination hX
  constructor
  · linear_combination hY
  · push_cast
    simp only [← SixQubit.star_mul_self]
    linear_combination hZ

private lemma col_normSq_six (z : ℂ) :
    Complex.normSq (6 * z) = 36 * Complex.normSq z := by
  rw [map_mul]
  norm_num [Complex.normSq_ofReal]

private lemma col_normSq_neg_six (z : ℂ) :
    Complex.normSq (-6 * z) = 36 * Complex.normSq z := by
  rw [map_mul]
  norm_num [Complex.normSq_ofReal]

/-- At the collinear endpoint, the three displayed *actual* Pauli traces
already carry raw Shor--Laflamme mass four. -/
theorem collinear_three_trace_sum (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    Complex.normSq (trProj ![c,d] tPX) +
      Complex.normSq (trProj ![c,d] tPY) +
      Complex.normSq (trProj ![c,d] tPZ) = 4 := by
  have rows := zero_angle_trace_rows c d hc hd hcode
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, hAt, hBt, hdeg, hedge⟩
  have hu' :
      Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1) =
        (1 / 6 : ℝ) := by
    simpa [uSpin, uMass, spinMass] using hu
  have hv' :
      Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) =
        (1 / 6 : ℝ) := by
    simpa [vSpin, vMass, spinMass] using hv
  have hwedge :
      uSpin c 0 * vSpin d 1 - uSpin c 1 * vSpin d 0 = 0 := by
    simpa only [perp_inner] using hcol
  have hmass :
      Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1) +
        Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) =
        (1 / 3 : ℝ) := by
    linarith [hu', hv']
  have hb := bloch_add_sq_eq_mass_sq_sub_wedge
    (uSpin c 0) (uSpin c 1) (vSpin d 0) (vSpin d 1)
  rw [hmass, hwedge, Complex.normSq_zero] at hb
  norm_num at hb
  rw [rows.1, rows.2.1, rows.2.2,
    col_normSq_six, col_normSq_neg_six, col_normSq_six]
  linear_combination 36 * hb

private def collinearPaulis : Finset (SS.PauliString 6) :=
  [tPX, tPY, tPZ].toFinset

private theorem collinearPaulis_subset_weight_one :
    collinearPaulis ⊆
      Finset.univ.filter (fun P : SS.PauliString 6 ↦ P.wt = 1) := by
  intro P hP
  simp only [collinearPaulis, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false] at hP
  rcases hP with h | h | h
  all_goals subst P
  all_goals simp

private lemma collinearPaulis_sum (F : SS.PauliString 6 → ℝ) :
    (∑ P ∈ collinearPaulis, F P) = F tPX + F tPY + F tPZ := by
  have hn : [tPX, tPY, tPZ].Nodup := by decide
  simpa [collinearPaulis, add_assoc] using (List.sum_toFinset F hn)

/-- The collinear endpoint forces the low-weight enumerator bound from three
weight-one Paulis.  The `Aco 2` term is added only through its definition as a
sum of nonnegative squared moduli. -/
theorem collinear_low_bound (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    4 ≤ Aco ![c,d] 1 + Aco ![c,d] 2 := by
  have hsum :
      (∑ P ∈ collinearPaulis,
        Complex.normSq (trProj ![c,d] P)) = 4 := by
    rw [collinearPaulis_sum]
    exact collinear_three_trace_sum c d hc hd hnc hnd hcode hcol
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg
    collinearPaulis_subset_weight_one
    (fun P hmem hnot ↦ Complex.normSq_nonneg (trProj ![c,d] P))
  unfold Aco at ⊢
  rw [hsum] at hsub
  have hA2 := SixQubit.Pin.Aco_nonneg ![c,d] 2
  unfold Aco at hA2
  linarith

/-- The existing enumerator classification consumes the endpoint bound with
no additional support, chart, or rank assumption. -/
theorem collinear_enumerator (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      SixQubit.Orbit7Family.IsFamilyA ![c,d] a ∧
      SixQubit.Orbit7Family.IsFamilyB ![c,d] a :=
  enumerator_of_low_bound c d hnc hnd hcode
    (collinear_low_bound c d hc hd hnc hnd hcode hcol)

/-! ## Literal rank-two pair marginal -/

/-- Collinearity plus the two exact extreme masses identifies the two
rank-one extreme matrices without choosing a phase for either spinor. -/
theorem collinear_extreme_outer_eq (c d : SS.State 6 ℂ)
    (hu : uMass c = 1 / 6) (hv : vMass d = 1 / 6)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    ∀ i j, U c i j = W d i j := by
  have hD : anchorD c d = 0 := by
    unfold anchorD
    rw [hcol]
    ring
  have hdec := anchor_decomposition c d hu
  have hvpar : ∀ i, vSpin d i = anchorC c d * uSpin c i := by
    intro i
    rw [hdec i, hD]
    ring
  have hunit := anchor_unit c d hu hv
  rw [hD] at hunit
  norm_num at hunit
  change anchorC c d * star (anchorC c d) = 1 at hunit
  intro i j
  unfold U W block outer
  change uSpin c i * star (uSpin c j) =
    vSpin d i * star (vSpin d j)
  rw [hvpar i, hvpar j, star_mul]
  calc
    uSpin c i * star (uSpin c j) =
        1 * (uSpin c i * star (uSpin c j)) := by ring
    _ = (anchorC c d * star (anchorC c d)) *
        (uSpin c i * star (uSpin c j)) := by rw [hunit]
    _ = anchorC c d * uSpin c i *
        (star (anchorC c d) * star (uSpin c j)) := by ring_nf
    _ = anchorC c d * uSpin c i *
        (star (uSpin c j) * star (anchorC c d)) := by
      rw [mul_comm (star (anchorC c d))]

/-- In the collinear branch every physical perpendicular edge coordinate
vanishes.  This is extracted term-by-term from the nonnegative global frame
sum, not asserted as a support ansatz. -/
theorem collinear_ycoord_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    ∀ e ∈ edgePairs, ycoord c d e = 0 := by
  have hwedge :
      vSpin d 0 * uSpin c 1 - vSpin d 1 * uSpin c 0 = 0 := by
    rw [perp_inner] at hcol
    linear_combination -hcol
  have hsum := perpendicular_frame_total c d hc hd hcode
  rw [hwedge, Complex.normSq_zero] at hsum
  norm_num at hsum
  intro e he
  have hle :
      Complex.normSq
          (spinInner (perpSpin (vSpin d))
            (spinor c (aBase e.1 e.2))) ≤
        ∑ f ∈ edgePairs,
          Complex.normSq
            (spinInner (perpSpin (vSpin d))
              (spinor c (aBase f.1 f.2))) :=
    Finset.single_le_sum
      (fun f _ ↦ Complex.normSq_nonneg
        (spinInner (perpSpin (vSpin d))
          (spinor c (aBase f.1 f.2)))) he
  rw [hsum] at hle
  have hz : Complex.normSq
      (spinInner (perpSpin (vSpin d))
        (spinor c (aBase e.1 e.2))) = 0 :=
    le_antisymm hle (Complex.normSq_nonneg _)
  simpa [ycoord] using Complex.normSq_eq_zero.mp hz

private lemma collinear_aMass_eq (c d : SS.State 6 ℂ)
    (e : Fin 5 × Fin 5) (hv : vMass d = 1 / 6)
    (hy : ycoord c d e = 0) :
    aMass c e.1 e.2 = 6 * Complex.normSq (xcoord c d e) := by
  have hL := SixQubit.Spinor.lagrange
    (vSpin d 0) (vSpin d 1)
    (spinor c (aBase e.1 e.2) 0)
    (spinor c (aBase e.1 e.2) 1)
  rw [← perp_inner (vSpin d) (spinor c (aBase e.1 e.2))] at hL
  change Complex.normSq (xcoord c d e) +
      Complex.normSq (ycoord c d e) =
        vMass d * aMass c e.1 e.2 at hL
  rw [hy, Complex.normSq_zero, hv] at hL
  linarith

private lemma collinear_AMat_eq (c d : SS.State 6 ℂ)
    (e : Fin 5 × Fin 5) (hv : vMass d = 1 / 6)
    (hy : ycoord c d e = 0) :
    ∀ i j, AMat c e i j =
      (6 * (aMass c e.1 e.2 : ℂ)) * W d i j := by
  have ha : ∀ i,
      spinor c (aBase e.1 e.2) i =
        6 * xcoord c d e * vSpin d i := by
    intro i
    rw [acoord_reconstruction c d hv e i, hy]
    ring
  have hm := collinear_aMass_eq c d e hv hy
  have hmC := congrArg (fun r : ℝ ↦ (r : ℂ)) hm
  push_cast at hmC
  have hxC :
      xcoord c d e * star (xcoord c d e) =
        (Complex.normSq (xcoord c d e) : ℂ) := by
    rw [mul_comm, SixQubit.star_mul_self]
  intro i j
  unfold AMat W block outer
  change spinor c (aBase e.1 e.2) i *
      star (spinor c (aBase e.1 e.2) j) =
    (6 * (aMass c e.1 e.2 : ℂ)) *
      (vSpin d i * star (vSpin d j))
  rw [ha i, ha j]
  calc
    (6 * xcoord c d e * vSpin d i) *
        star (6 * xcoord c d e * vSpin d j) =
      36 * (xcoord c d e * star (xcoord c d e)) *
        (vSpin d i * star (vSpin d j)) := by
          simp only [star_mul]
          norm_num
          ring
    _ = 36 * (Complex.normSq (xcoord c d e) : ℂ) *
        (vSpin d i * star (vSpin d j)) := by rw [hxC]
    _ = (6 * (aMass c e.1 e.2 : ℂ)) *
        (vSpin d i * star (vSpin d j)) := by rw [hmC]; ring

private lemma spinor_nonzero_index_of_mass_six (w : Spinor)
    (hw : Complex.normSq (w 0) + Complex.normSq (w 1) = 1 / 6) :
    ∃ i : Fin 2, w i ≠ 0 := by
  by_cases h0 : w 0 = 0
  · by_cases h1 : w 1 = 0
    · rw [h0, h1, Complex.normSq_zero] at hw
      norm_num at hw
    · exact ⟨1, h1⟩
  · exact ⟨0, h0⟩

/-- Every active coordinate has the manuscript's two explicit nonzero outer
blocks.  The first equality uses the nonnegative frame term-by-term; the
second then follows from the actual `star_identity`. -/
theorem collinear_pair_blocks_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    ∀ s,
      pairZeroBlock c s = scaledOuter (uSpin c) 3 ∧
      pairOneBlock d s = scaledOuter (vSpin d) 3 := by
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, hAt, hBt, hdeg, hedge⟩
  have hUW := collinear_extreme_outer_eq c d hu hv hcol
  have hy := collinear_ycoord_zero c d hc hd hcode hcol
  have hdegC : ∀ s,
      (∑ e ∈ incidentPairs s, (aMass c e.1 e.2 : ℂ)) = 1 / 3 := by
    intro s
    have hs := congrArg (fun r : ℝ ↦ (r : ℂ)) (hdeg s).1
    push_cast at hs
    simpa [degreeA] using hs
  have hstarA : ∀ s i j, starA c s i j = 2 * U c i j := by
    intro s i j
    unfold starA
    rw [Finset.sum_congr rfl (fun e he =>
      collinear_AMat_eq c d e hv (hy e (incident_subset s he)) i j)]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hdegC s]
    norm_num
    rw [← hUW i j]
  have hstarB : ∀ s i j, starB d s i j = 2 * W d i j := by
    intro s i j
    have hs := star_identity c d hc hd hcode s i j
    rw [hstarA s i j, hUW i j] at hs
    linear_combination hs
  intro s
  constructor
  · ext i j
    unfold pairZeroBlock scaledOuter
    rw [hstarA s i j]
    unfold U block outer
    unfold uSpin
    ring
  · ext i j
    unfold pairOneBlock scaledOuter
    rw [hstarB s i j]
    unfold W block outer
    unfold vSpin
    ring

/-- The literal `4 × 4` pair marginal is the block diagonal sum of two
scaled outer products at every active coordinate. -/
theorem collinear_pairMarginal_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    ∀ s, pairMarginal c d s =
      twoOuterBlocks (uSpin c) (vSpin d) 3 3 := by
  have hb := collinear_pair_blocks_normal_form c d hc hd hnc hnd hcode hcol
  intro s
  ext p q
  rcases p with ⟨pi, pk⟩
  rcases q with ⟨qi, qk⟩
  fin_cases pk <;> fin_cases qk <;>
    simp [pairMarginal, twoOuterBlocks, Matrix.blockDiagonal_apply,
      (hb s).1, (hb s).2]

/-- Each of the two physical diagonal blocks is nonzero and has literal
`Matrix.rank = 1`. -/
theorem collinear_pair_blocks_rank_one (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    ∀ s,
      IsNonzeroRankOneBlock (pairZeroBlock c s) ∧
      IsNonzeroRankOneBlock (pairOneBlock d s) := by
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, hAt, hBt, hdeg, hedge⟩
  have hu' :
      Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1) =
        (1 / 6 : ℝ) := by
    simpa [uSpin, uMass, spinMass] using hu
  have hv' :
      Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) =
        (1 / 6 : ℝ) := by
    simpa [vSpin, vMass, spinMass] using hv
  rcases spinor_nonzero_index_of_mass_six (uSpin c) hu' with ⟨iu, hiu⟩
  rcases spinor_nonzero_index_of_mass_six (vSpin d) hv' with ⟨iv, hiv⟩
  have hb := collinear_pair_blocks_normal_form c d hc hd hnc hnd hcode hcol
  intro s
  constructor
  · rw [(hb s).1]
    exact scaledOuter_isNonzeroRankOne (uSpin c) 3 iu hiu (by norm_num)
  · rw [(hb s).2]
    exact scaledOuter_isNonzeroRankOne (vSpin d) 3 iv hiv (by norm_num)

/-- The collinear endpoint has rank exactly two at every active coordinate,
not merely rank at most two. -/
theorem collinear_pair_rank_two_at (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    ∀ s, PairRankTwoAt c d s := by
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, hAt, hBt, hdeg, hedge⟩
  have hu' :
      Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1) =
        (1 / 6 : ℝ) := by
    simpa [uSpin, uMass, spinMass] using hu
  have hv' :
      Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) =
        (1 / 6 : ℝ) := by
    simpa [vSpin, vMass, spinMass] using hv
  rcases spinor_nonzero_index_of_mass_six (uSpin c) hu' with ⟨iu, hiu⟩
  rcases spinor_nonzero_index_of_mass_six (vSpin d) hv' with ⟨iv, hiv⟩
  intro s
  unfold PairRankTwoAt
  rw [collinear_pairMarginal_normal_form c d hc hd hnc hnd hcode hcol s]
  exact twoOuterBlocks_rank (uSpin c) (vSpin d) 3 3 iu iv
    hiu hiv (by norm_num) (by norm_num)

/-- Existential form of the manuscript's structural headline. -/
theorem collinear_has_pair_rank_two (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hcol : spinInner (perpSpin (uSpin c)) (vSpin d) = 0) :
    HasPairRankTwo c d :=
  ⟨0, collinear_pair_rank_two_at c d hc hd hnc hnd hcode hcol 0⟩

end

end SixQubit.Orbit7Universal
