import SixQubit.Orbit7UniversalScalar

/-!
# Orbit 7 universal converse, III: matrix-valued moments

This module derives the `2 x 2` spinor identities in the uniform orbit-7
presentation from the genuine Hilbert-space Knill--Laflamme predicate.  The
matrix entries are represented as functions `Fin 2 -> Fin 2 -> ℂ`; no basis
normalization, phase choice, or nonvanishing assumption is made.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize

noncomputable section

/-! ## Spinors and rank-one matrices -/

abbrev Spinor := Fin 2 -> ℂ
abbrev Mat2 := Fin 2 -> Fin 2 -> ℂ

/-- The two amplitudes differing only on the zero-angle coordinate `A`. -/
def spinor (f : SS.State 6 ℂ) (y : SS.BitString 6) : Spinor :=
  ![f y, f (SS.bxor y abit)]

/-- The rank-one matrix `s s^dagger`, entrywise. -/
def outer (s : Spinor) : Mat2 := fun i j => s i * star (s j)

def block (f : SS.State 6 ℂ) (y : SS.BitString 6) : Mat2 :=
  outer (spinor f y)

def U (c : SS.State 6 ℂ) : Mat2 := block c zero
def W (d : SS.State 6 ℂ) : Mat2 := block d activeAll
def AMat (c : SS.State 6 ℂ) (e : Fin 5 × Fin 5) : Mat2 :=
  block c (aBase e.1 e.2)
def BMat (d : SS.State 6 ℂ) (e : Fin 5 × Fin 5) : Mat2 :=
  block d (bBase e.1 e.2)

def sumA (c : SS.State 6 ℂ) : Mat2 := fun i j =>
  ∑ e ∈ edgePairs, AMat c e i j
def sumB (d : SS.State 6 ℂ) : Mat2 := fun i j =>
  ∑ e ∈ edgePairs, BMat d e i j

def starA (c : SS.State 6 ℂ) (v : Fin 5) : Mat2 := fun i j =>
  ∑ e ∈ incidentPairs v, AMat c e i j
def starB (d : SS.State 6 ℂ) (v : Fin 5) : Mat2 := fun i j =>
  ∑ e ∈ incidentPairs v, BMat d e i j

def rhoC (c : SS.State 6 ℂ) : Mat2 := fun i j => U c i j + sumA c i j
def rhoD (d : SS.State 6 ℂ) : Mat2 := fun i j => sumB d i j + W d i j

@[simp] lemma spinor_zero (f : SS.State 6 ℂ) (y : SS.BitString 6) :
    spinor f y 0 = f y := rfl

@[simp] lemma spinor_one (f : SS.State 6 ℂ) (y : SS.BitString 6) :
    spinor f y 1 = f (SS.bxor y abit) := rfl

/-! ## Exact decompositions of the two full fibres -/

private theorem S0_blocks : S0 = spinSupport zero ∪ aShellSupport := by decide
private theorem S2_blocks : S2 = bShellSupport ∪ spinSupport activeAll := by decide
private theorem S0_blocks_disjoint : Disjoint (spinSupport zero) aShellSupport := by decide
private theorem S2_blocks_disjoint : Disjoint bShellSupport (spinSupport activeAll) := by decide

private lemma sum_aShell (F : SS.BitString 6 -> ℂ) :
    (∑ x ∈ aShellSupport, F x) =
      ∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2), F x := by
  unfold aShellSupport
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact aShell_disjoint e he f hf hef)]

private lemma sum_bShell (F : SS.BitString 6 -> ℂ) :
    (∑ x ∈ bShellSupport, F x) =
      ∑ e ∈ edgePairs, ∑ x ∈ spinSupport (bBase e.1 e.2), F x := by
  unfold bShellSupport
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact bShell_disjoint e he f hf hef)]

private lemma sum_S0_blocks (F : SS.BitString 6 -> ℂ) :
    (∑ x ∈ S0, F x) =
      (∑ x ∈ spinSupport zero, F x) +
        ∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2), F x := by
  rw [S0_blocks, Finset.sum_union S0_blocks_disjoint, sum_aShell]

private lemma sum_S2_blocks (F : SS.BitString 6 -> ℂ) :
    (∑ x ∈ S2, F x) =
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (bBase e.1 e.2), F x) +
        ∑ x ∈ spinSupport activeAll, F x := by
  rw [S2_blocks, Finset.sum_union S2_blocks_disjoint, sum_bShell]

private theorem zero_eq_zeroMask : zero = (fun _ => false) := by decide
private theorem abit_eq_basis : abit = SS.stdBasis (0 : Fin 6) := by decide
private theorem bdot_zero : ∀ x : SS.BitString 6, SS.bdot zero x = false := by decide
private theorem bdot_false : ∀ x : SS.BitString 6,
    SS.bdot (fun _ => false) x = false := by decide

private lemma flip_flip (y : SS.BitString 6) :
    SS.bxor (SS.bxor y abit) abit = y := SS.bxor_bxor_cancel y abit

private lemma flip_flip' (y : SS.BitString 6) :
    SS.bxor abit (SS.bxor y abit) = y := by
  rw [SS.bxor_comm abit, flip_flip]

private theorem S0_closed_zero :
    S0.filter (fun x => SS.bxor x zero ∈ S0) = S0 := by decide
private theorem S2_closed_zero :
    S2.filter (fun x => SS.bxor x zero ∈ S2) = S2 := by decide
private theorem S0_closed_abit :
    S0.filter (fun x => SS.bxor x abit ∈ S0) = S0 := by decide
private theorem S2_closed_abit :
    S2.filter (fun x => SS.bxor x abit ∈ S2) = S2 := by decide

private theorem base_bit_zero :
    zero 0 = false ∧ activeAll 0 = false ∧
      (∀ e ∈ edgePairs, aBase e.1 e.2 0 = false) ∧
      (∀ e ∈ edgePairs, bBase e.1 e.2 0 = false) := by decide

private lemma bdot_abit_base (y : SS.BitString 6) (hy : y 0 = false) :
    SS.bdot abit y = false := by
  rw [abit_eq_basis, bdot_stdBasis, hy]

private lemma bdot_abit_flip (y : SS.BitString 6) (hy : y 0 = false) :
    SS.bdot abit (SS.bxor y abit) = true := by
  rw [abit_eq_basis, bdot_stdBasis]
  simp [SS.bxor, SS.stdBasis, hy]

private lemma block_I (f : SS.State 6 ℂ) (y : SS.BitString 6) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot zero x) (star (f (SS.bxor x zero)) * f x)) =
      block f y 0 0 + block f y 1 1 := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  simp [spinSupport, block, outer, spinor, zero_eq_zeroMask, hne, bdot_false]
  ring

private lemma block_Z (f : SS.State 6 ℂ) (y : SS.BitString 6)
    (hy : y 0 = false) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot abit x) (star (f (SS.bxor x zero)) * f x)) =
      block f y 0 0 - block f y 1 1 := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  have h0 := bdot_abit_base y hy
  have h1 := bdot_abit_flip y hy
  simp [spinSupport, block, outer, spinor, zero_eq_zeroMask, hne, h0, h1]
  ring

private lemma block_X (f : SS.State 6 ℂ) (y : SS.BitString 6) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot zero x) (star (f (SS.bxor x abit)) * f x)) =
      block f y 0 1 + block f y 1 0 := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  simp [spinSupport, block, outer, spinor, zero_eq_zeroMask, hne,
    bdot_false, flip_flip']
  ring

private lemma block_XZ (f : SS.State 6 ℂ) (y : SS.BitString 6)
    (hy : y 0 = false) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot abit x) (star (f (SS.bxor x abit)) * f x)) =
      block f y 0 1 - block f y 1 0 := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  have h0 := bdot_abit_base y hy
  have h1 := bdot_abit_flip y hy
  simp [spinSupport, block, outer, spinor, hne, h0, h1,
    flip_flip']
  ring

/-! ## The undressed reduced matrix -/

private lemma diag_I_c (c : SS.State 6 ℂ) :
    diagOn S0 c zero zero = rhoC c 0 0 + rhoC c 1 1 := by
  unfold diagOn
  rw [S0_closed_zero, sum_S0_blocks, block_I]
  simp_rw [block_I]
  rw [Finset.sum_add_distrib]
  unfold rhoC U sumA AMat
  ring

private lemma diag_I_d (d : SS.State 6 ℂ) :
    diagOn S2 d zero zero = rhoD d 0 0 + rhoD d 1 1 := by
  unfold diagOn
  rw [S2_closed_zero, sum_S2_blocks]
  simp_rw [block_I]
  rw [Finset.sum_add_distrib]
  unfold rhoD W sumB BMat
  ring

private lemma diag_Z_c (c : SS.State 6 ℂ) :
    diagOn S0 c zero abit = rhoC c 0 0 - rhoC c 1 1 := by
  unfold diagOn
  rw [S0_closed_zero, sum_S0_blocks,
    block_Z c zero base_bit_zero.1]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2),
        signMul (SS.bdot abit x) (star (c (SS.bxor x zero)) * c x)) =
      ∑ e ∈ edgePairs,
        (block c (aBase e.1 e.2) 0 0 - block c (aBase e.1 e.2) 1 1) := by
    exact Finset.sum_congr rfl (fun e he =>
      block_Z c (aBase e.1 e.2) (base_bit_zero.2.2.1 e he))
  rw [hs, Finset.sum_sub_distrib]
  unfold rhoC U sumA AMat
  ring

private lemma diag_Z_d (d : SS.State 6 ℂ) :
    diagOn S2 d zero abit = rhoD d 0 0 - rhoD d 1 1 := by
  unfold diagOn
  rw [S2_closed_zero, sum_S2_blocks]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (bBase e.1 e.2),
        signMul (SS.bdot abit x) (star (d (SS.bxor x zero)) * d x)) =
      ∑ e ∈ edgePairs,
        (block d (bBase e.1 e.2) 0 0 - block d (bBase e.1 e.2) 1 1) := by
    exact Finset.sum_congr rfl (fun e he =>
      block_Z d (bBase e.1 e.2) (base_bit_zero.2.2.2 e he))
  rw [hs, Finset.sum_sub_distrib,
    block_Z d activeAll base_bit_zero.2.1]
  unfold rhoD W sumB BMat
  ring

private lemma diag_X_c (c : SS.State 6 ℂ) :
    diagOn S0 c abit zero = rhoC c 0 1 + rhoC c 1 0 := by
  unfold diagOn
  rw [S0_closed_abit, sum_S0_blocks, block_X]
  simp_rw [block_X]
  rw [Finset.sum_add_distrib]
  unfold rhoC U sumA AMat
  ring

private lemma diag_X_d (d : SS.State 6 ℂ) :
    diagOn S2 d abit zero = rhoD d 0 1 + rhoD d 1 0 := by
  unfold diagOn
  rw [S2_closed_abit, sum_S2_blocks]
  simp_rw [block_X]
  rw [Finset.sum_add_distrib]
  unfold rhoD W sumB BMat
  ring

private lemma diag_XZ_c (c : SS.State 6 ℂ) :
    diagOn S0 c abit abit = rhoC c 0 1 - rhoC c 1 0 := by
  unfold diagOn
  rw [S0_closed_abit, sum_S0_blocks,
    block_XZ c zero base_bit_zero.1]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2),
        signMul (SS.bdot abit x) (star (c (SS.bxor x abit)) * c x)) =
      ∑ e ∈ edgePairs,
        (block c (aBase e.1 e.2) 0 1 - block c (aBase e.1 e.2) 1 0) := by
    exact Finset.sum_congr rfl (fun e he =>
      block_XZ c (aBase e.1 e.2) (base_bit_zero.2.2.1 e he))
  rw [hs, Finset.sum_sub_distrib]
  unfold rhoC U sumA AMat
  ring

private lemma diag_XZ_d (d : SS.State 6 ℂ) :
    diagOn S2 d abit abit = rhoD d 0 1 - rhoD d 1 0 := by
  unfold diagOn
  rw [S2_closed_abit, sum_S2_blocks]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (bBase e.1 e.2),
        signMul (SS.bdot abit x) (star (d (SS.bxor x abit)) * d x)) =
      ∑ e ∈ edgePairs,
        (block d (bBase e.1 e.2) 0 1 - block d (bBase e.1 e.2) 1 0) := by
    exact Finset.sum_congr rfl (fun e he =>
      block_XZ d (bBase e.1 e.2) (base_bit_zero.2.2.2 e he))
  rw [hs, Finset.sum_sub_distrib,
    block_XZ d activeAll base_bit_zero.2.1]
  unfold rhoD W sumB BMat
  ring

/-- The identity operator and the three Pauli operators on the zero-angle
coordinate reconstruct the common reduced state on that coordinate. -/
theorem common_reduced (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ i j, rhoC c i j = rhoD d i j := by
  have hcS := full_support0 hc
  have hdS := full_support2 hd
  have row (e z : SS.BitString 6)
      (hw : (⟨e,z⟩ : SS.PauliString 6).wt ≤ 2) :
      diagOn S0 c e z = diagOn S2 d e z :=
    diagOn_eq_of_hasDistance S0 S2 c d hcS hdS hcode e z hw
  have hI := row zero zero (by decide)
  have hZ := row zero abit (by decide)
  have hX := row abit zero (by decide)
  have hXZ := row abit abit (by decide)
  rw [diag_I_c, diag_I_d] at hI
  rw [diag_Z_c, diag_Z_d] at hZ
  rw [diag_X_c, diag_X_d] at hX
  rw [diag_XZ_c, diag_XZ_d] at hXZ
  intro i j
  fin_cases i <;> fin_cases j
  · change rhoC c 0 0 = rhoD d 0 0
    linear_combination (1/2) * hI + (1/2) * hZ
  · change rhoC c 0 1 = rhoD d 0 1
    linear_combination (1/2) * hX + (1/2) * hXZ
  · change rhoC c 1 0 = rhoD d 1 0
    linear_combination (1/2) * hX - (1/2) * hXZ
  · change rhoC c 1 1 = rhoD d 1 1
    linear_combination (1/2) * hI - (1/2) * hZ

/-! ## One-active-`Z` dressings -/

def vmask (v : Fin 5) : SS.BitString 6 := SS.stdBasis v.succ
def Avmask (v : Fin 5) : SS.BitString 6 := SS.bxor abit (vmask v)

private theorem abit_active_false : ∀ v : Fin 5, abit v.succ = false := by decide
private theorem zero_active_false : ∀ v : Fin 5, zero v.succ = false := by decide
private theorem activeAll_active_true : ∀ v : Fin 5, activeAll v.succ = true := by decide

private lemma flip_active_bit (y : SS.BitString 6) (v : Fin 5) :
    SS.bxor y abit v.succ = y v.succ := by
  rw [SS.bxor_apply, abit_active_false, Bool.xor_false]

private lemma block_Iv (f : SS.State 6 ℂ) (y : SS.BitString 6) (v : Fin 5) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot (vmask v) x) (star (f (SS.bxor x zero)) * f x)) =
      signMul (y v.succ) (block f y 0 0 + block f y 1 1) := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  rw [show SS.bdot (vmask v) y = y v.succ by
      simp [vmask, bdot_stdBasis],
    show SS.bdot (vmask v) (SS.bxor y abit) = y v.succ by
      rw [vmask, bdot_stdBasis, flip_active_bit]]
  by_cases h : y v.succ = true <;>
    simp [block, outer, spinor, zero_eq_zeroMask, h] <;> ring

private lemma block_Zv (f : SS.State 6 ℂ) (y : SS.BitString 6) (v : Fin 5)
    (hy : y 0 = false) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot (Avmask v) x) (star (f (SS.bxor x zero)) * f x)) =
      signMul (y v.succ) (block f y 0 0 - block f y 1 1) := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  have hA0 := bdot_abit_base y hy
  have hA1 := bdot_abit_flip y hy
  have hv0 : SS.bdot (vmask v) y = y v.succ := by
    simp [vmask, bdot_stdBasis]
  have hv1 : SS.bdot (vmask v) (SS.bxor y abit) = y v.succ := by
    rw [vmask, bdot_stdBasis, flip_active_bit]
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  rw [show SS.bdot (Avmask v) y = xor false (y v.succ) by
      simp [Avmask, bdot_bxor_left, hA0, hv0],
    show SS.bdot (Avmask v) (SS.bxor y abit) = xor true (y v.succ) by
      simp [Avmask, bdot_bxor_left, hA1, hv1]]
  by_cases h : y v.succ = true <;>
    simp [block, outer, spinor, zero_eq_zeroMask, h] <;> ring

private lemma block_Xv (f : SS.State 6 ℂ) (y : SS.BitString 6) (v : Fin 5) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot (vmask v) x) (star (f (SS.bxor x abit)) * f x)) =
      signMul (y v.succ) (block f y 0 1 + block f y 1 0) := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  rw [show SS.bdot (vmask v) y = y v.succ by
      simp [vmask, bdot_stdBasis],
    show SS.bdot (vmask v) (SS.bxor y abit) = y v.succ by
      rw [vmask, bdot_stdBasis, flip_active_bit]]
  by_cases h : y v.succ = true <;>
    simp [block, outer, spinor, h, flip_flip'] <;> ring

private lemma block_XZv (f : SS.State 6 ℂ) (y : SS.BitString 6) (v : Fin 5)
    (hy : y 0 = false) :
    (∑ x ∈ spinSupport y,
      signMul (SS.bdot (Avmask v) x) (star (f (SS.bxor x abit)) * f x)) =
      signMul (y v.succ) (block f y 0 1 - block f y 1 0) := by
  have hne : y ≠ SS.bxor y abit := Ne.symm (spin_flip_ne y)
  have hA0 := bdot_abit_base y hy
  have hA1 := bdot_abit_flip y hy
  have hv0 : SS.bdot (vmask v) y = y v.succ := by
    simp [vmask, bdot_stdBasis]
  have hv1 : SS.bdot (vmask v) (SS.bxor y abit) = y v.succ := by
    rw [vmask, bdot_stdBasis, flip_active_bit]
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton]
  rw [show SS.bdot (Avmask v) y = xor false (y v.succ) by
      simp [Avmask, bdot_bxor_left, hA0, hv0],
    show SS.bdot (Avmask v) (SS.bxor y abit) = xor true (y v.succ) by
      simp [Avmask, bdot_bxor_left, hA1, hv1]]
  by_cases h : y v.succ = true <;>
    simp [block, outer, spinor, h, flip_flip'] <;> ring

private theorem aBase_false_iff : ∀ v : Fin 5, ∀ e ∈ edgePairs,
    aBase e.1 e.2 v.succ = false ↔ e ∈ incidentPairs v := by decide

private theorem bBase_true_iff : ∀ v : Fin 5, ∀ e ∈ edgePairs,
    bBase e.1 e.2 v.succ = true ↔ e ∈ incidentPairs v := by decide

private lemma sum_ite_incident (F : Fin 5 × Fin 5 -> ℂ) (v : Fin 5) :
    (∑ e ∈ edgePairs, if e ∈ incidentPairs v then F e else 0) =
      ∑ e ∈ incidentPairs v, F e := by
  symm
  calc
    (∑ e ∈ incidentPairs v, F e) =
        ∑ e ∈ incidentPairs v, if e ∈ incidentPairs v then F e else 0 := by simp
    _ = ∑ e ∈ edgePairs, if e ∈ incidentPairs v then F e else 0 := by
      apply Finset.sum_subset (incident_subset v)
      intro e he hnot
      simp [hnot]

private lemma signed_sum_a (F : Fin 5 × Fin 5 -> ℂ) (v : Fin 5) :
    (∑ e ∈ edgePairs, signMul (aBase e.1 e.2 v.succ) (F e)) =
      2 * (∑ e ∈ incidentPairs v, F e) - ∑ e ∈ edgePairs, F e := by
  have ht : ∀ e ∈ edgePairs,
      signMul (aBase e.1 e.2 v.succ) (F e) =
        2 * (if e ∈ incidentPairs v then F e else 0) - F e := by
    intro e he
    by_cases hi : e ∈ incidentPairs v
    · have hb : aBase e.1 e.2 v.succ = false :=
        (aBase_false_iff v e he).2 hi
      simp [hb, hi]
      ring
    · have hb : aBase e.1 e.2 v.succ = true := by
        cases hbit : aBase e.1 e.2 v.succ with
        | false => exact absurd ((aBase_false_iff v e he).1 hbit) hi
        | true => rfl
      simp [hb, hi]
  calc
    _ = ∑ e ∈ edgePairs,
        (2 * (if e ∈ incidentPairs v then F e else 0) - F e) :=
      Finset.sum_congr rfl ht
    _ = 2 * (∑ e ∈ edgePairs, if e ∈ incidentPairs v then F e else 0) -
        ∑ e ∈ edgePairs, F e := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [sum_ite_incident]

private lemma signed_sum_b (F : Fin 5 × Fin 5 -> ℂ) (v : Fin 5) :
    (∑ e ∈ edgePairs, signMul (bBase e.1 e.2 v.succ) (F e)) =
      (∑ e ∈ edgePairs, F e) - 2 * ∑ e ∈ incidentPairs v, F e := by
  have ht : ∀ e ∈ edgePairs,
      signMul (bBase e.1 e.2 v.succ) (F e) =
        F e - 2 * (if e ∈ incidentPairs v then F e else 0) := by
    intro e he
    by_cases hi : e ∈ incidentPairs v
    · have hb : bBase e.1 e.2 v.succ = true :=
        (bBase_true_iff v e he).2 hi
      simp [hb, hi]
      ring
    · have hb : bBase e.1 e.2 v.succ = false := by
        cases hbit : bBase e.1 e.2 v.succ with
        | false => rfl
        | true => exact absurd ((bBase_true_iff v e he).1 hbit) hi
      simp [hb, hi]
  calc
    _ = ∑ e ∈ edgePairs,
        (F e - 2 * (if e ∈ incidentPairs v then F e else 0)) :=
      Finset.sum_congr rfl ht
    _ = (∑ e ∈ edgePairs, F e) -
        2 * (∑ e ∈ edgePairs, if e ∈ incidentPairs v then F e else 0) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = _ := by rw [sum_ite_incident]

def signedC (c : SS.State 6 ℂ) (v : Fin 5) : Mat2 := fun i j =>
  U c i j + 2 * starA c v i j - sumA c i j

def signedD (d : SS.State 6 ℂ) (v : Fin 5) : Mat2 := fun i j =>
  sumB d i j - 2 * starB d v i j - W d i j

private lemma diag_Iv_c (c : SS.State 6 ℂ) (v : Fin 5) :
    diagOn S0 c zero (vmask v) = signedC c v 0 0 + signedC c v 1 1 := by
  unfold diagOn
  rw [S0_closed_zero, sum_S0_blocks, block_Iv]
  simp_rw [block_Iv]
  rw [signed_sum_a, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hz : zero v.succ = false := zero_active_false v
  rw [hz, signMul_false]
  unfold signedC U starA sumA AMat
  ring

private lemma diag_Iv_d (d : SS.State 6 ℂ) (v : Fin 5) :
    diagOn S2 d zero (vmask v) = signedD d v 0 0 + signedD d v 1 1 := by
  unfold diagOn
  rw [S2_closed_zero, sum_S2_blocks]
  simp_rw [block_Iv]
  rw [signed_sum_b, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hv : activeAll v.succ = true := activeAll_active_true v
  rw [hv, signMul_true]
  unfold signedD W starB sumB BMat
  ring

private lemma diag_Zv_c (c : SS.State 6 ℂ) (v : Fin 5) :
    diagOn S0 c zero (Avmask v) = signedC c v 0 0 - signedC c v 1 1 := by
  unfold diagOn
  rw [S0_closed_zero, sum_S0_blocks,
    block_Zv c zero v base_bit_zero.1]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2),
        signMul (SS.bdot (Avmask v) x) (star (c (SS.bxor x zero)) * c x)) =
      ∑ e ∈ edgePairs, signMul (aBase e.1 e.2 v.succ)
        (block c (aBase e.1 e.2) 0 0 - block c (aBase e.1 e.2) 1 1) := by
    exact Finset.sum_congr rfl (fun e he =>
      block_Zv c (aBase e.1 e.2) v (base_bit_zero.2.2.1 e he))
  rw [hs, signed_sum_a, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hz : zero v.succ = false := zero_active_false v
  rw [hz, signMul_false]
  unfold signedC U starA sumA AMat
  ring

private lemma diag_Zv_d (d : SS.State 6 ℂ) (v : Fin 5) :
    diagOn S2 d zero (Avmask v) = signedD d v 0 0 - signedD d v 1 1 := by
  unfold diagOn
  rw [S2_closed_zero, sum_S2_blocks]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (bBase e.1 e.2),
        signMul (SS.bdot (Avmask v) x) (star (d (SS.bxor x zero)) * d x)) =
      ∑ e ∈ edgePairs, signMul (bBase e.1 e.2 v.succ)
        (block d (bBase e.1 e.2) 0 0 - block d (bBase e.1 e.2) 1 1) := by
    exact Finset.sum_congr rfl (fun e he =>
      block_Zv d (bBase e.1 e.2) v (base_bit_zero.2.2.2 e he))
  rw [hs, signed_sum_b, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    block_Zv d activeAll v base_bit_zero.2.1]
  have hv : activeAll v.succ = true := activeAll_active_true v
  rw [hv, signMul_true]
  unfold signedD W starB sumB BMat
  ring

private lemma diag_Xv_c (c : SS.State 6 ℂ) (v : Fin 5) :
    diagOn S0 c abit (vmask v) = signedC c v 0 1 + signedC c v 1 0 := by
  unfold diagOn
  rw [S0_closed_abit, sum_S0_blocks, block_Xv]
  simp_rw [block_Xv]
  rw [signed_sum_a, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hz : zero v.succ = false := zero_active_false v
  rw [hz, signMul_false]
  unfold signedC U starA sumA AMat
  ring

private lemma diag_Xv_d (d : SS.State 6 ℂ) (v : Fin 5) :
    diagOn S2 d abit (vmask v) = signedD d v 0 1 + signedD d v 1 0 := by
  unfold diagOn
  rw [S2_closed_abit, sum_S2_blocks]
  simp_rw [block_Xv]
  rw [signed_sum_b, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hv : activeAll v.succ = true := activeAll_active_true v
  rw [hv, signMul_true]
  unfold signedD W starB sumB BMat
  ring

private lemma diag_XZv_c (c : SS.State 6 ℂ) (v : Fin 5) :
    diagOn S0 c abit (Avmask v) = signedC c v 0 1 - signedC c v 1 0 := by
  unfold diagOn
  rw [S0_closed_abit, sum_S0_blocks,
    block_XZv c zero v base_bit_zero.1]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (aBase e.1 e.2),
        signMul (SS.bdot (Avmask v) x) (star (c (SS.bxor x abit)) * c x)) =
      ∑ e ∈ edgePairs, signMul (aBase e.1 e.2 v.succ)
        (block c (aBase e.1 e.2) 0 1 - block c (aBase e.1 e.2) 1 0) := by
    exact Finset.sum_congr rfl (fun e he =>
      block_XZv c (aBase e.1 e.2) v (base_bit_zero.2.2.1 e he))
  rw [hs, signed_sum_a, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hz : zero v.succ = false := zero_active_false v
  rw [hz, signMul_false]
  unfold signedC U starA sumA AMat
  ring

private lemma diag_XZv_d (d : SS.State 6 ℂ) (v : Fin 5) :
    diagOn S2 d abit (Avmask v) = signedD d v 0 1 - signedD d v 1 0 := by
  unfold diagOn
  rw [S2_closed_abit, sum_S2_blocks]
  have hs :
      (∑ e ∈ edgePairs, ∑ x ∈ spinSupport (bBase e.1 e.2),
        signMul (SS.bdot (Avmask v) x) (star (d (SS.bxor x abit)) * d x)) =
      ∑ e ∈ edgePairs, signMul (bBase e.1 e.2 v.succ)
        (block d (bBase e.1 e.2) 0 1 - block d (bBase e.1 e.2) 1 0) := by
    exact Finset.sum_congr rfl (fun e he =>
      block_XZv d (bBase e.1 e.2) v (base_bit_zero.2.2.2 e he))
  rw [hs, signed_sum_b, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    block_XZv d activeAll v base_bit_zero.2.1]
  have hv : activeAll v.succ = true := activeAll_active_true v
  rw [hv, signMul_true]
  unfold signedD W starB sumB BMat
  ring

/-- The four `Z_v`-dressed Pauli rows reconstruct the dressed reduced matrix. -/
theorem signed_reduced (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ v i j, signedC c v i j = signedD d v i j := by
  have hcS := full_support0 hc
  have hdS := full_support2 hd
  intro v
  have row (e z : SS.BitString 6)
      (hw : (⟨e,z⟩ : SS.PauliString 6).wt ≤ 2) :
      diagOn S0 c e z = diagOn S2 d e z :=
    diagOn_eq_of_hasDistance S0 S2 c d hcS hdS hcode e z hw
  have hI := row zero (vmask v) (by
    fin_cases v <;> decide)
  have hZ := row zero (Avmask v) (by
    fin_cases v <;> decide)
  have hX := row abit (vmask v) (by
    fin_cases v <;> decide)
  have hXZ := row abit (Avmask v) (by
    fin_cases v <;> decide)
  rw [diag_Iv_c, diag_Iv_d] at hI
  rw [diag_Zv_c, diag_Zv_d] at hZ
  rw [diag_Xv_c, diag_Xv_d] at hX
  rw [diag_XZv_c, diag_XZv_d] at hXZ
  intro i j
  fin_cases i <;> fin_cases j
  · change signedC c v 0 0 = signedD d v 0 0
    linear_combination (1/2) * hI + (1/2) * hZ
  · change signedC c v 0 1 = signedD d v 0 1
    linear_combination (1/2) * hX + (1/2) * hXZ
  · change signedC c v 1 0 = signedD d v 1 0
    linear_combination (1/2) * hX - (1/2) * hXZ
  · change signedC c v 1 1 = signedD d v 1 1
    linear_combination (1/2) * hI - (1/2) * hZ

/-! ## The manuscript matrix normal form -/

/-- The `Z_v`-dressed identity before summing over the five active vertices:
`A_v + B_v = rho_A - U - W`, entrywise. -/
theorem prestar_identity (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ v i j, starA c v i j + starB d v i j =
      rhoC c i j - U c i j - W d i j := by
  intro v i j
  have hr := common_reduced c d hc hd hcode i j
  have hz := signed_reduced c d hc hd hcode v i j
  unfold signedC signedD at hz
  unfold rhoC at hr ⊢
  unfold rhoD at hr
  linear_combination (1/2) * hz - (1/2) * hr

private lemma sum_starA (c : SS.State 6 ℂ) (i j : Fin 2) :
    (∑ v : Fin 5, starA c v i j) = 2 * sumA c i j := by
  rw [show (∑ v : Fin 5, starA c v i j) =
      starA c 0 i j + starA c 1 i j + starA c 2 i j +
        starA c 3 i j + starA c 4 i j by
          simp [Fin.sum_univ_succ]
          ring]
  unfold starA sumA
  rw [show incidentPairs 0 = ({(0,1),(0,2),(0,3),(0,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    show incidentPairs 1 = ({(0,1),(1,2),(1,3),(1,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    show incidentPairs 2 = ({(0,2),(1,2),(2,3),(2,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    show incidentPairs 3 = ({(0,3),(1,3),(2,3),(3,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    show incidentPairs 4 = ({(0,4),(1,4),(2,4),(3,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    edgePairs_eq]
  simp [tenEdges]
  ring

private lemma sum_starB (d : SS.State 6 ℂ) (i j : Fin 2) :
    (∑ v : Fin 5, starB d v i j) = 2 * sumB d i j := by
  rw [show (∑ v : Fin 5, starB d v i j) =
      starB d 0 i j + starB d 1 i j + starB d 2 i j +
        starB d 3 i j + starB d 4 i j by
          simp [Fin.sum_univ_succ]
          ring]
  unfold starB sumB
  rw [show incidentPairs 0 = ({(0,1),(0,2),(0,3),(0,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    show incidentPairs 1 = ({(0,1),(1,2),(1,3),(1,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    show incidentPairs 2 = ({(0,2),(1,2),(2,3),(2,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    show incidentPairs 3 = ({(0,3),(1,3),(2,3),(3,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    show incidentPairs 4 = ({(0,4),(1,4),(2,4),(3,4)} :
      Finset (Fin 5 × Fin 5)) by decide,
    edgePairs_eq]
  simp [tenEdges]
  ring

/-- Summing `prestar_identity` over `K_5` gives the central manuscript
identity `rho_A = 3 (U + W)`, entrywise. -/
theorem rho_identity (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ i j, rhoC c i j = 3 * (U c i j + W d i j) := by
  intro i j
  have hs :
      (∑ v : Fin 5, (starA c v i j + starB d v i j)) =
        ∑ v : Fin 5, (rhoC c i j - U c i j - W d i j) :=
    Finset.sum_congr rfl (fun v _ => prestar_identity c d hc hd hcode v i j)
  rw [Finset.sum_add_distrib, sum_starA, sum_starB] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hs
  norm_num at hs
  have hr := common_reduced c d hc hd hcode i j
  unfold rhoC at hr ⊢
  unfold rhoD at hr
  unfold rhoC at hs
  linear_combination -hs - 2 * hr

/-- The two global edge-frame identities of the manuscript. -/
theorem global_frames (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    (∀ i j, sumA c i j = 2 * U c i j + 3 * W d i j) ∧
      (∀ i j, sumB d i j = 3 * U c i j + 2 * W d i j) := by
  constructor
  · intro i j
    have hr := rho_identity c d hc hd hcode i j
    unfold rhoC at hr
    linear_combination hr
  · intro i j
    have hr := rho_identity c d hc hd hcode i j
    have hcρ := common_reduced c d hc hd hcode i j
    unfold rhoC at hr hcρ
    unfold rhoD at hcρ
    linear_combination hr - hcρ

/-- The final star identity `A_v + B_v = 2 (U + W)`, entrywise. -/
theorem star_identity (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ v i j, starA c v i j + starB d v i j =
      2 * (U c i j + W d i j) := by
  intro v i j
  have hp := prestar_identity c d hc hd hcode v i j
  have hr := rho_identity c d hc hd hcode i j
  rw [hp, hr]
  ring

/-- Six concrete one- and two-qubit diagonal sums in the rank-two-pair
branch.  They are the three Bloch coordinates on the zero-angle qubit,
without and with a `Z_v` dressing.  This public wrapper exposes the actual
support-sum content needed by the enumerator argument while keeping the
block-decomposition implementation lemmas private. -/
theorem target_diag_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) (v : Fin 5)
    (hA : ∀ i j, starA c v i j = 2 * U c i j) :
    diagOn S0 c abit zero + diagOn S2 d abit zero =
        6 * ((U c 0 1 + U c 1 0) + (W d 0 1 + W d 1 0)) ∧
    diagOn S0 c abit abit + diagOn S2 d abit abit =
        6 * ((U c 0 1 - U c 1 0) + (W d 0 1 - W d 1 0)) ∧
    diagOn S0 c zero abit + diagOn S2 d zero abit =
        6 * ((U c 0 0 - U c 1 1) + (W d 0 0 - W d 1 1)) ∧
    diagOn S0 c abit (vmask v) + diagOn S2 d abit (vmask v) =
        6 * ((U c 0 1 + U c 1 0) - (W d 0 1 + W d 1 0)) ∧
    diagOn S0 c abit (Avmask v) + diagOn S2 d abit (Avmask v) =
        6 * ((U c 0 1 - U c 1 0) - (W d 0 1 - W d 1 0)) ∧
    diagOn S0 c zero (Avmask v) + diagOn S2 d zero (Avmask v) =
        6 * ((U c 0 0 - U c 1 1) - (W d 0 0 - W d 1 1)) := by
  have hr := rho_identity c d hc hd hcode
  have hcρ := common_reduced c d hc hd hcode
  have hs := signed_reduced c d hc hd hcode
  have hf := (global_frames c d hc hd hcode).1
  have hsC : ∀ i j, signedC c v i j =
      3 * (U c i j - W d i j) := by
    intro i j
    unfold signedC
    rw [hA i j, hf i j]
    ring
  constructor
  · rw [diag_X_c, diag_X_d]
    linear_combination 2 * hr 0 1 + 2 * hr 1 0 - hcρ 0 1 - hcρ 1 0
  constructor
  · rw [diag_XZ_c, diag_XZ_d]
    linear_combination 2 * hr 0 1 - 2 * hr 1 0 - hcρ 0 1 + hcρ 1 0
  constructor
  · rw [diag_Z_c, diag_Z_d]
    linear_combination 2 * hr 0 0 - 2 * hr 1 1 - hcρ 0 0 + hcρ 1 1
  constructor
  · rw [diag_Xv_c, diag_Xv_d]
    linear_combination 2 * hsC 0 1 + 2 * hsC 1 0 - hs v 0 1 - hs v 1 0
  constructor
  · rw [diag_XZv_c, diag_XZv_d]
    linear_combination 2 * hsC 0 1 - 2 * hsC 1 0 - hs v 0 1 + hs v 1 0
  · rw [diag_Zv_c, diag_Zv_d]
    linear_combination 2 * hsC 0 0 - 2 * hsC 1 1 - hs v 0 0 + hs v 1 1

/-! ## Cross-KL identities -/

def spinInner (s t : Spinor) : ℂ := star (s 0) * t 0 + star (s 1) * t 1

private lemma off_spin_block (f g : SS.State 6 ℂ)
    (source target flip : SS.BitString 6)
    (hmap : SS.bxor source flip = target) :
    (∑ x ∈ spinSupport source, star (f (SS.bxor x flip)) * g x) =
      spinInner (spinor f target) (spinor g source) := by
  have hne : source ≠ SS.bxor source abit := Ne.symm (spin_flip_ne source)
  have hmapA : SS.bxor (SS.bxor source abit) flip = SS.bxor target abit := by
    rw [SS.bxor_assoc, SS.bxor_comm abit flip, ← SS.bxor_assoc, hmap]
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    hmap, hmapA]
  unfold spinInner spinor
  rfl

private theorem pair_incidence : ∀ e ∈ edgePairs,
    S2.filter (fun y => SS.bxor y (activeEdge e.1 e.2) ∈ S0) =
      spinSupport (bBase e.1 e.2) ∪ spinSupport activeAll := by decide

private theorem pair_map_bottom : ∀ e ∈ edgePairs,
    SS.bxor (bBase e.1 e.2) (activeEdge e.1 e.2) = zero := by decide

private theorem pair_map_top : ∀ e ∈ edgePairs,
    SS.bxor activeAll (activeEdge e.1 e.2) = aBase e.1 e.2 := by decide

private theorem pair_pauli_weight : ∀ e ∈ edgePairs,
    (⟨activeEdge e.1 e.2, zero⟩ : SS.PauliString 6).wt ≤ 2 := by decide

private lemma paircross_expansion (c d : SS.State 6 ℂ)
    (e : Fin 5 × Fin 5) (he : e ∈ edgePairs) :
    offSumOn S0 S2 c d (activeEdge e.1 e.2) zero =
      spinInner (spinor c zero) (spinor d (bBase e.1 e.2)) +
        spinInner (spinor c (aBase e.1 e.2)) (spinor d activeAll) := by
  unfold offSumOn
  rw [pair_incidence e he, Finset.sum_union (bPair_disjoint e he)]
  have hplain (source : SS.BitString 6) :
      (∑ x ∈ spinSupport source,
        signMul (SS.bdot zero x)
          (star (c (SS.bxor x (activeEdge e.1 e.2))) * d x)) =
        ∑ x ∈ spinSupport source,
          star (c (SS.bxor x (activeEdge e.1 e.2))) * d x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [bdot_zero, signMul_false]
  rw [hplain, hplain,
    off_spin_block c d (bBase e.1 e.2) zero (activeEdge e.1 e.2)
      (pair_map_bottom e he),
    off_spin_block c d activeAll (aBase e.1 e.2) (activeEdge e.1 e.2)
      (pair_map_top e he)]

/-- The manuscript's physical-pair cross equation
`u^dagger b_e + a_e^dagger v = 0`, for every edge of `K_5`. -/
theorem paircross (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ e ∈ edgePairs,
      spinInner (spinor c zero) (spinor d (bBase e.1 e.2)) +
        spinInner (spinor c (aBase e.1 e.2)) (spinor d activeAll) = 0 := by
  have hcS := full_support0 hc
  have hdS := full_support2 hd
  intro e he
  have hrow := offSumOn_eq_zero_of_hasDistance S0 S2 c d hcS hdS hcode
    (activeEdge e.1 e.2) zero (pair_pauli_weight e he)
  rw [paircross_expansion c d e he] at hrow
  exact hrow

/-! ## The one-active-flip matrix -/

/-- The oriented perfect-matching sum in the manuscript.  For a nonincident
edge `f`, flipping `v` sends its active pattern to the complement of the unique
edge paired with `f` in a perfect matching of `V \ {v}`. -/
def oneFlipMat (c d : SS.State 6 ℂ) (v : Fin 5) : Mat2 := fun p q =>
  ∑ f ∈ nonincidentPairs v,
    spinor d (bBase f.1 f.2) p *
      star (spinor c (SS.bxor (bBase f.1 f.2) (vmask v)) q)

private theorem oneflip_incidence : ∀ v : Fin 5,
    S2.filter (fun y => SS.bxor y (vmask v) ∈ S0) =
      bSupportFor (nonincidentPairs v) := by decide

private theorem oneflipA_incidence : ∀ v : Fin 5,
    S2.filter (fun y => SS.bxor y (Avmask v) ∈ S0) =
      bSupportFor (nonincidentPairs v) := by decide

private lemma nonincident_subset_edges (v : Fin 5) :
    nonincidentPairs v ⊆ edgePairs := nonincident_subset v

private def crossBlock (c d : SS.State 6 ℂ) (source : SS.BitString 6)
    (v : Fin 5) : Mat2 := fun p q =>
  spinor d source p * star (spinor c (SS.bxor source (vmask v)) q)

private lemma cross_block_I (c d : SS.State 6 ℂ)
    (source : SS.BitString 6) (v : Fin 5) :
    (∑ x ∈ spinSupport source,
      star (c (SS.bxor x (vmask v))) * d x) =
      crossBlock c d source v 0 0 + crossBlock c d source v 1 1 := by
  have hne : source ≠ SS.bxor source abit := Ne.symm (spin_flip_ne source)
  have hcomm :
      SS.bxor (SS.bxor source abit) (vmask v) =
        SS.bxor (SS.bxor source (vmask v)) abit := by
    rw [SS.bxor_assoc, SS.bxor_comm abit (vmask v), ← SS.bxor_assoc]
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton, hcomm]
  unfold crossBlock spinor
  simp
  all_goals ring

private lemma source_Av (source : SS.BitString 6) (v : Fin 5) :
    SS.bxor source (Avmask v) =
      SS.bxor (SS.bxor source (vmask v)) abit := by
  unfold Avmask
  rw [SS.bxor_comm abit (vmask v), ← SS.bxor_assoc]

private lemma sourceA_Av (source : SS.BitString 6) (v : Fin 5) :
    SS.bxor (SS.bxor source abit) (Avmask v) =
      SS.bxor source (vmask v) := by
  rw [SS.bxor_assoc, Avmask, ← SS.bxor_assoc abit abit,
    SS.bxor_self, SS.zero_bxor]

private lemma cross_block_X (c d : SS.State 6 ℂ)
    (source : SS.BitString 6) (v : Fin 5) :
    (∑ x ∈ spinSupport source,
      star (c (SS.bxor x (Avmask v))) * d x) =
      crossBlock c d source v 0 1 + crossBlock c d source v 1 0 := by
  have hne : source ≠ SS.bxor source abit := Ne.symm (spin_flip_ne source)
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    source_Av, sourceA_Av]
  unfold crossBlock spinor
  simp
  all_goals ring

private lemma cross_block_Z (c d : SS.State 6 ℂ)
    (source : SS.BitString 6) (v : Fin 5) (h0 : source 0 = false) :
    (∑ x ∈ spinSupport source,
      signMul (SS.bdot abit x) (star (c (SS.bxor x (vmask v))) * d x)) =
      crossBlock c d source v 0 0 - crossBlock c d source v 1 1 := by
  have hne : source ≠ SS.bxor source abit := Ne.symm (spin_flip_ne source)
  have hb0 := bdot_abit_base source h0
  have hb1 := bdot_abit_flip source h0
  have hcomm :
      SS.bxor (SS.bxor source abit) (vmask v) =
        SS.bxor (SS.bxor source (vmask v)) abit := by
    rw [SS.bxor_assoc, SS.bxor_comm abit (vmask v), ← SS.bxor_assoc]
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    hb0, hb1, signMul_false, signMul_true, hcomm]
  unfold crossBlock spinor
  simp
  all_goals ring

private lemma cross_block_XZ (c d : SS.State 6 ℂ)
    (source : SS.BitString 6) (v : Fin 5) (h0 : source 0 = false) :
    (∑ x ∈ spinSupport source,
      signMul (SS.bdot abit x) (star (c (SS.bxor x (Avmask v))) * d x)) =
      crossBlock c d source v 0 1 - crossBlock c d source v 1 0 := by
  have hne : source ≠ SS.bxor source abit := Ne.symm (spin_flip_ne source)
  have hb0 := bdot_abit_base source h0
  have hb1 := bdot_abit_flip source h0
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton,
    hb0, hb1, signMul_false, signMul_true, source_Av, sourceA_Av]
  unfold crossBlock spinor
  simp
  all_goals ring

private lemma oneflip_plain_sum (c d : SS.State 6 ℂ) (v : Fin 5) :
    offSumOn S0 S2 c d (vmask v) zero =
      oneFlipMat c d v 0 0 + oneFlipMat c d v 1 1 := by
  unfold offSumOn
  rw [oneflip_incidence v]
  unfold bSupportFor
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact bShell_disjoint e (nonincident_subset_edges v he)
      f (nonincident_subset_edges v hf) hef)]
  have hplain (source : SS.BitString 6) :
      (∑ x ∈ spinSupport source,
        signMul (SS.bdot zero x) (star (c (SS.bxor x (vmask v))) * d x)) =
      ∑ x ∈ spinSupport source, star (c (SS.bxor x (vmask v))) * d x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [bdot_zero, signMul_false]
  simp_rw [hplain, cross_block_I]
  rw [Finset.sum_add_distrib]
  unfold oneFlipMat crossBlock
  rfl

private lemma oneflip_Z_sum (c d : SS.State 6 ℂ) (v : Fin 5) :
    offSumOn S0 S2 c d (vmask v) abit =
      oneFlipMat c d v 0 0 - oneFlipMat c d v 1 1 := by
  unfold offSumOn
  rw [oneflip_incidence v]
  unfold bSupportFor
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact bShell_disjoint e (nonincident_subset_edges v he)
      f (nonincident_subset_edges v hf) hef)]
  have hs :
      (∑ e ∈ nonincidentPairs v, ∑ x ∈ spinSupport (bBase e.1 e.2),
        signMul (SS.bdot abit x) (star (c (SS.bxor x (vmask v))) * d x)) =
      ∑ e ∈ nonincidentPairs v,
        (crossBlock c d (bBase e.1 e.2) v 0 0 -
          crossBlock c d (bBase e.1 e.2) v 1 1) := by
    exact Finset.sum_congr rfl (fun e he => cross_block_Z c d
      (bBase e.1 e.2) v (base_bit_zero.2.2.2 e (nonincident_subset_edges v he)))
  rw [hs, Finset.sum_sub_distrib]
  unfold oneFlipMat crossBlock
  rfl

private lemma oneflip_X_sum (c d : SS.State 6 ℂ) (v : Fin 5) :
    offSumOn S0 S2 c d (Avmask v) zero =
      oneFlipMat c d v 0 1 + oneFlipMat c d v 1 0 := by
  unfold offSumOn
  rw [oneflipA_incidence v]
  unfold bSupportFor
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact bShell_disjoint e (nonincident_subset_edges v he)
      f (nonincident_subset_edges v hf) hef)]
  have hplain (source : SS.BitString 6) :
      (∑ x ∈ spinSupport source,
        signMul (SS.bdot zero x) (star (c (SS.bxor x (Avmask v))) * d x)) =
      ∑ x ∈ spinSupport source, star (c (SS.bxor x (Avmask v))) * d x := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [bdot_zero, signMul_false]
  simp_rw [hplain, cross_block_X]
  rw [Finset.sum_add_distrib]
  unfold oneFlipMat crossBlock
  rfl

private lemma oneflip_XZ_sum (c d : SS.State 6 ℂ) (v : Fin 5) :
    offSumOn S0 S2 c d (Avmask v) abit =
      oneFlipMat c d v 0 1 - oneFlipMat c d v 1 0 := by
  unfold offSumOn
  rw [oneflipA_incidence v]
  unfold bSupportFor
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact bShell_disjoint e (nonincident_subset_edges v he)
      f (nonincident_subset_edges v hf) hef)]
  have hs :
      (∑ e ∈ nonincidentPairs v, ∑ x ∈ spinSupport (bBase e.1 e.2),
        signMul (SS.bdot abit x) (star (c (SS.bxor x (Avmask v))) * d x)) =
      ∑ e ∈ nonincidentPairs v,
        (crossBlock c d (bBase e.1 e.2) v 0 1 -
          crossBlock c d (bBase e.1 e.2) v 1 0) := by
    exact Finset.sum_congr rfl (fun e he => cross_block_XZ c d
      (bBase e.1 e.2) v (base_bit_zero.2.2.2 e (nonincident_subset_edges v he)))
  rw [hs, Finset.sum_sub_distrib]
  unfold oneFlipMat crossBlock
  rfl

/-- The complete `2 x 2` one-active-flip cross matrix vanishes.  This is the
entrywise form of the three perfect-matching hafnian matrix in the manuscript. -/
theorem oneflip_matrix (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ v p q, oneFlipMat c d v p q = 0 := by
  have hcS := full_support0 hc
  have hdS := full_support2 hd
  intro v
  have row (e z : SS.BitString 6)
      (hw : (⟨e,z⟩ : SS.PauliString 6).wt ≤ 2) :
      offSumOn S0 S2 c d e z = 0 :=
    offSumOn_eq_zero_of_hasDistance S0 S2 c d hcS hdS hcode e z hw
  have hI := row (vmask v) zero (by fin_cases v <;> decide)
  have hZ := row (vmask v) abit (by fin_cases v <;> decide)
  have hX := row (Avmask v) zero (by fin_cases v <;> decide)
  have hXZ := row (Avmask v) abit (by fin_cases v <;> decide)
  rw [oneflip_plain_sum] at hI
  rw [oneflip_Z_sum] at hZ
  rw [oneflip_X_sum] at hX
  rw [oneflip_XZ_sum] at hXZ
  intro p q
  fin_cases p <;> fin_cases q
  · change oneFlipMat c d v 0 0 = 0
    linear_combination (1/2) * hI + (1/2) * hZ
  · change oneFlipMat c d v 0 1 = 0
    linear_combination (1/2) * hX + (1/2) * hXZ
  · change oneFlipMat c d v 1 0 = 0
    linear_combination (1/2) * hX - (1/2) * hXZ
  · change oneFlipMat c d v 1 1 = 0
    linear_combination (1/2) * hI - (1/2) * hZ

/-! ## Active-Z dressings and the disjoint-edge relation -/

/-- The scalar cross term contributed by the oriented edge `f` to the
one-active-flip row at `v`.  When `e,f` are the complementary edges of the
four-set away from `v`, this is `a_e^dagger b_f`. -/
def oneFlipInner (c d : SS.State 6 ℂ) (v : Fin 5)
    (f : Fin 5 × Fin 5) : ℂ :=
  spinInner (spinor c (SS.bxor (bBase f.1 f.2) (vmask v)))
    (spinor d (bBase f.1 f.2))

/-- The trace of the one-flip matrix with a `Z` dressing on active vertex
`j`.  This is only a scalar row: adding an arbitrary operator on `A` as well
would have physical weight three. -/
def oneFlipSigned (c d : SS.State 6 ℂ) (v j : Fin 5) : ℂ :=
  ∑ f ∈ nonincidentPairs v,
    signMul (SS.bdot (vmask j) (bBase f.1 f.2)) (oneFlipInner c d v f)

private lemma bdot_vmask_flip_abit (j : Fin 5) (source : SS.BitString 6) :
    SS.bdot (vmask j) (SS.bxor source abit) =
      SS.bdot (vmask j) source := by
  rw [SS.bdot_bxor_right]
  have hz : SS.bdot (vmask j) abit = false := by
    fin_cases j <;> decide
  rw [hz]
  simp

private lemma cross_block_activeZ (c d : SS.State 6 ℂ)
    (source : SS.BitString 6) (v j : Fin 5) :
    (∑ x ∈ spinSupport source,
      signMul (SS.bdot (vmask j) x)
        (star (c (SS.bxor x (vmask v))) * d x)) =
      signMul (SS.bdot (vmask j) source)
        (spinInner (spinor c (SS.bxor source (vmask v)))
          (spinor d source)) := by
  have hne : source ≠ SS.bxor source abit := Ne.symm (spin_flip_ne source)
  have hs := bdot_vmask_flip_abit j source
  unfold spinSupport
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton, hs]
  unfold spinInner spinor
  have hmap :
      SS.bxor (SS.bxor source abit) (vmask v) =
        SS.bxor (SS.bxor source (vmask v)) abit := by
    rw [SS.bxor_assoc, SS.bxor_comm abit (vmask v), ← SS.bxor_assoc]
  rw [hmap]
  by_cases hsign : SS.bdot (vmask j) source = true
  · rw [hsign, signMul_true]
    simp [signMul]
    ring
  · have hfalse : SS.bdot (vmask j) source = false := Bool.eq_false_of_not_eq_true hsign
    rw [hfalse, signMul_false]
    simp [signMul]

private lemma oneflip_activeZ_sum (c d : SS.State 6 ℂ) (v j : Fin 5) :
    offSumOn S0 S2 c d (vmask v) (vmask j) = oneFlipSigned c d v j := by
  unfold offSumOn
  rw [oneflip_incidence v]
  unfold bSupportFor
  rw [Finset.sum_biUnion (by
    intro e he f hf hef
    exact bShell_disjoint e (nonincident_subset_edges v he)
      f (nonincident_subset_edges v hf) hef)]
  simp_rw [cross_block_activeZ]
  unfold oneFlipSigned oneFlipInner
  rfl

/-- Every active-`Z` dressed scalar one-flip system vanishes, directly from
the genuine distance-three predicate.  The Pauli has weight one when `v=j`
and weight two otherwise. -/
theorem oneflip_signed_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ v j, oneFlipSigned c d v j = 0 := by
  have hcS := full_support0 hc
  have hdS := full_support2 hd
  intro v j
  have hrow := offSumOn_eq_zero_of_hasDistance S0 S2 c d hcS hdS hcode
    (vmask v) (vmask j) (by fin_cases v <;> fin_cases j <;> decide)
  rw [oneflip_activeZ_sum] at hrow
  exact hrow

/-- `e` and `f` are the two complementary edges in the four active vertices
away from `v`.  The bit-string equations record the two orientations needed
below rather than trusting a graph-complement convention. -/
def PairedAt (v : Fin 5) (e f : Fin 5 × Fin 5) : Prop :=
  e ∈ nonincidentPairs v ∧ f ∈ nonincidentPairs v ∧ e ≠ f ∧
    f ∈ nonincidentBoth e

private instance pairedAtDecidable (v : Fin 5) (e f : Fin 5 × Fin 5) :
    Decidable (PairedAt v e f) := by
  unfold PairedAt
  infer_instance

private theorem disjoint_has_remaining : ∀ e ∈ edgePairs,
    ∀ f ∈ nonincidentBoth e, ∃ v, PairedAt v e f := by
  rintro ⟨e₁, e₂⟩ he ⟨f₁, f₂⟩ hf
  have h : ∀ e₁ e₂ f₁ f₂ : Fin 5,
      (e₁, e₂) ∈ edgePairs → (f₁, f₂) ∈ nonincidentBoth (e₁, e₂) →
        ∃ v, PairedAt v (e₁, e₂) (f₁, f₂) := by
    decide
  exact h e₁ e₂ f₁ f₂ he hf

private theorem paired_maps_pointwise : ∀ v e f, PairedAt v e f →
    (∀ k, SS.bxor (bBase e.1 e.2) (vmask v) k = aBase f.1 f.2 k) ∧
      (∀ k, SS.bxor (bBase f.1 f.2) (vmask v) k = aBase e.1 e.2 k) := by
  rintro v ⟨e₁, e₂⟩ ⟨f₁, f₂⟩ hpair
  have h : ∀ (v e₁ e₂ f₁ f₂ : Fin 5),
      PairedAt v (e₁, e₂) (f₁, f₂) →
        (∀ k, SS.bxor (bBase e₁ e₂) (vmask v) k = aBase f₁ f₂ k) ∧
          (∀ k, SS.bxor (bBase f₁ f₂) (vmask v) k = aBase e₁ e₂ k) := by
    decide
  exact h v e₁ e₂ f₁ f₂ hpair

private def epsZ (b : Bool) : ℤ := if b then -1 else 1

private lemma signMul_eq_epsZ (b : Bool) (z : ℂ) :
    signMul b z = (epsZ b : ℂ) * z := by
  cases b <;> simp [epsZ]

/-- Adding the two dressings at the endpoints of `e` isolates precisely the
two orientations of the complementary matching `{e,f}`.  This is a finite
`K_5` incidence fact, checked by kernel reduction. -/
private theorem paired_sign_coefficient : ∀ v e f, PairedAt v e f →
    ∀ g ∈ nonincidentPairs v,
      epsZ (SS.bdot (vmask e.1) (bBase g.1 g.2)) +
        epsZ (SS.bdot (vmask e.2) (bBase g.1 g.2)) =
          if g = e then -2 else if g = f then 2 else 0 := by
  rintro v ⟨e₁, e₂⟩ ⟨f₁, f₂⟩ hpair ⟨g₁, g₂⟩ hg
  have h : ∀ (v e₁ e₂ f₁ f₂ g₁ g₂ : Fin 5),
      PairedAt v (e₁, e₂) (f₁, f₂) → (g₁, g₂) ∈ nonincidentPairs v →
        epsZ (SS.bdot (vmask e₁) (bBase g₁ g₂)) +
          epsZ (SS.bdot (vmask e₂) (bBase g₁ g₂)) =
            if (g₁, g₂) = (e₁, e₂) then -2
            else if (g₁, g₂) = (f₁, f₂) then 2 else 0 := by
    decide
  exact h v e₁ e₂ f₁ f₂ g₁ g₂ hpair hg

private lemma sum_two_indicators {α : Type} [DecidableEq α]
    (E : Finset α) (e f : α) (he : e ∈ E) (hf : f ∈ E) (hef : e ≠ f)
    (F : α → ℂ) :
    (∑ g ∈ E, (((if g = e then -2 else if g = f then 2 else 0 : ℤ) : ℂ) * F g)) =
      -2 * F e + 2 * F f := by
  calc
    (∑ g ∈ E, (((if g = e then -2 else if g = f then 2 else 0 : ℤ) : ℂ) * F g)) =
        ∑ g ∈ E,
          ((if g = e then (-2 : ℂ) * F g else 0) +
            (if g = f then (2 : ℂ) * F g else 0)) := by
      refine Finset.sum_congr rfl (fun g hg => ?_)
      split_ifs <;> simp_all
    _ = -2 * F e + 2 * F f := by
      rw [Finset.sum_add_distrib]
      simp [he, hf]

private lemma isolate_paired (c d : SS.State 6 ℂ) (v : Fin 5)
    (e f : Fin 5 × Fin 5) (hpair : PairedAt v e f) :
    oneFlipSigned c d v e.1 + oneFlipSigned c d v e.2 =
      -2 * oneFlipInner c d v e + 2 * oneFlipInner c d v f := by
  rcases hpair with ⟨he, hf, hef, hdis⟩
  unfold oneFlipSigned
  rw [← Finset.sum_add_distrib]
  calc
    (∑ g ∈ nonincidentPairs v,
      (signMul (SS.bdot (vmask e.1) (bBase g.1 g.2)) (oneFlipInner c d v g) +
       signMul (SS.bdot (vmask e.2) (bBase g.1 g.2)) (oneFlipInner c d v g))) =
        ∑ g ∈ nonincidentPairs v,
          ((epsZ (SS.bdot (vmask e.1) (bBase g.1 g.2)) +
            epsZ (SS.bdot (vmask e.2) (bBase g.1 g.2)) : ℤ) : ℂ) *
              oneFlipInner c d v g := by
      refine Finset.sum_congr rfl (fun g hg => ?_)
      rw [signMul_eq_epsZ, signMul_eq_epsZ]
      push_cast
      ring
    _ = ∑ g ∈ nonincidentPairs v,
          (((if g = e then -2 else if g = f then 2 else 0 : ℤ) : ℂ) *
            oneFlipInner c d v g) := by
      refine Finset.sum_congr rfl (fun g hg => ?_)
      rw [paired_sign_coefficient v e f
        ⟨he, hf, hef, hdis⟩ g hg]
    _ = -2 * oneFlipInner c d v e + 2 * oneFlipInner c d v f :=
      sum_two_indicators (nonincidentPairs v) e f he hf hef (oneFlipInner c d v)

/-- The manuscript's active-`Z` consequence
`a_e^dagger b_f = a_f^dagger b_e` for every pair of disjoint `K_5` edges.
It is derived from two actual weight-at-most-two KL rows, not assumed. -/
theorem disjoint_relation (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ e ∈ edgePairs, ∀ f ∈ nonincidentBoth e,
      spinInner (spinor c (aBase e.1 e.2)) (spinor d (bBase f.1 f.2)) =
        spinInner (spinor c (aBase f.1 f.2)) (spinor d (bBase e.1 e.2)) := by
  intro e he f hf
  obtain ⟨v, hpair⟩ := disjoint_has_remaining e he f hf
  have hz := oneflip_signed_zero c d hc hd hcode
  have hiso := isolate_paired c d v e f hpair
  rw [hz v e.1, hz v e.2] at hiso
  have horient : oneFlipInner c d v f = oneFlipInner c d v e := by
    have htwo : 2 * oneFlipInner c d v f = 2 * oneFlipInner c d v e := by
      linear_combination -hiso
    calc
      oneFlipInner c d v f = (1 / 2 : ℂ) * (2 * oneFlipInner c d v f) := by ring
      _ = (1 / 2 : ℂ) * (2 * oneFlipInner c d v e) := by rw [htwo]
      _ = oneFlipInner c d v e := by ring
  have hmaps := paired_maps_pointwise v e f hpair
  have hmapE : SS.bxor (bBase e.1 e.2) (vmask v) = aBase f.1 f.2 :=
    funext hmaps.1
  have hmapF : SS.bxor (bBase f.1 f.2) (vmask v) = aBase e.1 e.2 :=
    funext hmaps.2
  unfold oneFlipInner at horient
  rw [hmapF, hmapE] at horient
  exact horient

end

end SixQubit.Orbit7Universal
