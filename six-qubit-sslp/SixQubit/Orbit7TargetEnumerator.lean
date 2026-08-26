import SixQubit.Orbit7Boundary
import SixQubit.Orbit7UniversalEnum
import SixQubit.Orbit7Spinor

/-!
# Orbit 7: the target-star enumerator closure

The rank-two-pair star identity produces six actual Pauli traces: the three
Bloch coordinates on the zero-angle qubit, with and without a `Z_v`
dressing.  Their exact squared sum is four in the raw `Aco` convention.
Since all six Paulis have weight one or two, this proves the lower bound
consumed by `enumerator_of_low_bound`.
-/

namespace SixQubit.Orbit7Universal

open scoped BigOperators ComplexConjugate
open SixQubit SixQubit.Realize SS.MacWilliams

noncomputable section

set_option maxRecDepth 10000

def tPX : SS.PauliString 6 := ⟨abit, zero⟩
def tPY : SS.PauliString 6 := ⟨abit, abit⟩
def tPZ : SS.PauliString 6 := ⟨zero, abit⟩
def tPXv (v : Fin 5) : SS.PauliString 6 := ⟨abit, vmask v⟩
def tPYv (v : Fin 5) : SS.PauliString 6 := ⟨abit, Avmask v⟩
def tPZv (v : Fin 5) : SS.PauliString 6 := ⟨zero, Avmask v⟩

def targetPaulis (v : Fin 5) : Finset (SS.PauliString 6) :=
  [tPX, tPY, tPZ, tPXv v, tPYv v, tPZv v].toFinset

def targetLowPaulis : Finset (SS.PauliString 6) :=
  Finset.univ.filter (fun P => P.wt = 1) ∪
    Finset.univ.filter (fun P => P.wt = 2)

@[simp] private theorem tPX_wt : tPX.wt = 1 := by decide
@[simp] private theorem tPY_wt : tPY.wt = 1 := by decide
@[simp] private theorem tPZ_wt : tPZ.wt = 1 := by decide
@[simp] private theorem tPXv_wt : ∀ v, (tPXv v).wt = 2 := by decide
@[simp] private theorem tPYv_wt : ∀ v, (tPYv v).wt = 2 := by decide
@[simp] private theorem tPZv_wt : ∀ v, (tPZv v).wt = 2 := by decide
@[simp] private theorem tPX_numY : tPX.numY = 0 := by decide
@[simp] private theorem tPY_numY : tPY.numY = 1 := by decide
@[simp] private theorem tPZ_numY : tPZ.numY = 0 := by decide
@[simp] private theorem tPXv_numY : ∀ v, (tPXv v).numY = 0 := by decide
@[simp] private theorem tPYv_numY : ∀ v, (tPYv v).numY = 1 := by decide
@[simp] private theorem tPZv_numY : ∀ v, (tPZv v).numY = 0 := by decide

private theorem targetPaulis_subset : ∀ v, targetPaulis v ⊆ targetLowPaulis := by
  intro v P hP
  simp only [targetPaulis, List.mem_toFinset] at hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with h | h | h | h | h | h
  all_goals subst P
  all_goals simp [targetLowPaulis]

private lemma targetLowPaulis_sum (psi : Fin 2 → SS.State 6 ℂ) :
    (∑ P ∈ targetLowPaulis, Complex.normSq (trProj psi P)) =
      Aco psi 1 + Aco psi 2 := by
  have hdis : Disjoint
      (Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 1))
      (Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 2)) := by
    rw [Finset.disjoint_left]
    intro P h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  unfold targetLowPaulis Aco
  exact Finset.sum_union hdis

private lemma targetPaulis_sum (v : Fin 5) (F : SS.PauliString 6 → ℝ) :
    (∑ P ∈ targetPaulis v, F P) =
      F tPX + F tPY + F tPZ + F (tPXv v) + F (tPYv v) + F (tPZv v) := by
  have hn : [tPX, tPY, tPZ, tPXv v, tPYv v, tPZv v].Nodup := by
    fin_cases v <;> decide
  simpa [targetPaulis, add_assoc] using (List.sum_toFinset F hn)

/-- Projector traces on the two logical states are the two support sums with
the genuine Pauli `i^{#Y}` prefactor retained. -/
private lemma trProj_diagOn (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (P : SS.PauliString 6) :
    trProj ![c,d] P = Complex.I ^ P.numY *
      (diagOn S0 c P.x P.z + diagOn S2 d P.x P.z) := by
  rw [trProj, Fin.sum_univ_two]
  change SS.innerC c (SS.pauliAct P c) +
      SS.innerC d (SS.pauliAct P d) = _
  rw [innerC_eq_diagOn S0 c (full_support0 hc) P,
    innerC_eq_diagOn S2 d (full_support2 hd) P]
  ring

/-- The six concrete low-weight projector traces furnished by a target star.
The signs on the `Y` rows retain the library's genuine `i^{#Y}` prefactor. -/
theorem target_trace_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hcode : SS.HasDistance ![c,d] 3) (v : Fin 5)
    (hA : ∀ i j, starA c v i j = 2 * U c i j) :
    trProj ![c,d] tPX = 6 *
        (SixQubit.Orbit7Spinor.bx (uSpin c 0) (uSpin c 1) +
          SixQubit.Orbit7Spinor.bx (vSpin d 0) (vSpin d 1)) ∧
    trProj ![c,d] tPY = -6 *
        (SixQubit.Orbit7Spinor.by' (uSpin c 0) (uSpin c 1) +
          SixQubit.Orbit7Spinor.by' (vSpin d 0) (vSpin d 1)) ∧
    trProj ![c,d] tPZ = 6 *
        (SixQubit.Orbit7Spinor.bz (uSpin c 0) (uSpin c 1) +
          SixQubit.Orbit7Spinor.bz (vSpin d 0) (vSpin d 1)) ∧
    trProj ![c,d] (tPXv v) = 6 *
        (SixQubit.Orbit7Spinor.bx (uSpin c 0) (uSpin c 1) -
          SixQubit.Orbit7Spinor.bx (vSpin d 0) (vSpin d 1)) ∧
    trProj ![c,d] (tPYv v) = -6 *
        (SixQubit.Orbit7Spinor.by' (uSpin c 0) (uSpin c 1) -
          SixQubit.Orbit7Spinor.by' (vSpin d 0) (vSpin d 1)) ∧
    trProj ![c,d] (tPZv v) = 6 *
        (SixQubit.Orbit7Spinor.bz (uSpin c 0) (uSpin c 1) -
          SixQubit.Orbit7Spinor.bz (vSpin d 0) (vSpin d 1)) := by
  have rows := target_diag_rows c d hc hd hcode v hA
  have hX := trProj_diagOn c d hc hd tPX
  have hY := trProj_diagOn c d hc hd tPY
  have hZ := trProj_diagOn c d hc hd tPZ
  have hXv := trProj_diagOn c d hc hd (tPXv v)
  have hYv := trProj_diagOn c d hc hd (tPYv v)
  have hZv := trProj_diagOn c d hc hd (tPZv v)
  change trProj ![c,d] tPX = Complex.I ^ tPX.numY *
    (diagOn S0 c abit zero + diagOn S2 d abit zero) at hX
  change trProj ![c,d] tPY = Complex.I ^ tPY.numY *
    (diagOn S0 c abit abit + diagOn S2 d abit abit) at hY
  change trProj ![c,d] tPZ = Complex.I ^ tPZ.numY *
    (diagOn S0 c zero abit + diagOn S2 d zero abit) at hZ
  change trProj ![c,d] (tPXv v) = Complex.I ^ (tPXv v).numY *
    (diagOn S0 c abit (vmask v) + diagOn S2 d abit (vmask v)) at hXv
  change trProj ![c,d] (tPYv v) = Complex.I ^ (tPYv v).numY *
    (diagOn S0 c abit (Avmask v) + diagOn S2 d abit (Avmask v)) at hYv
  change trProj ![c,d] (tPZv v) = Complex.I ^ (tPZv v).numY *
    (diagOn S0 c zero (Avmask v) + diagOn S2 d zero (Avmask v)) at hZv
  rw [rows.1] at hX
  rw [rows.2.1] at hY
  rw [rows.2.2.1] at hZ
  rw [rows.2.2.2.1] at hXv
  rw [rows.2.2.2.2.1] at hYv
  rw [rows.2.2.2.2.2] at hZv
  simp only [tPX_numY, tPY_numY, tPZ_numY, tPXv_numY, tPYv_numY,
    tPZv_numY, pow_zero, pow_one, one_mul] at hX hY hZ hXv hYv hZv
  have expand : ∀ (i j : Fin 2),
      U c i j = uSpin c i * star (uSpin c j) ∧
      W d i j = vSpin d i * star (vSpin d j) := by
    intro i j
    exact ⟨rfl, rfl⟩
  simp only [expand] at hX hY hZ hXv hYv hZv
  unfold SixQubit.Orbit7Spinor.bx SixQubit.Orbit7Spinor.by'
    SixQubit.Orbit7Spinor.bz
  constructor
  · linear_combination hX
  constructor
  · linear_combination hY
  constructor
  · push_cast
    simp only [← SixQubit.star_mul_self]
    linear_combination hZ
  constructor
  · linear_combination hXv
  constructor
  · linear_combination hYv
  · push_cast
    simp only [← SixQubit.star_mul_self]
    linear_combination hZv

private lemma normSq_six (z : ℂ) :
    Complex.normSq (6 * z) = 36 * Complex.normSq z := by
  rw [map_mul]
  norm_num [Complex.normSq_ofReal]

private lemma normSq_neg_six (z : ℂ) :
    Complex.normSq (-6 * z) = 36 * Complex.normSq z := by
  rw [map_mul]
  norm_num [Complex.normSq_ofReal]

/-- The six explicitly listed low-weight Paulis carry exactly raw `A`-mass
four.  This is the two-qubit reduced-purity statement expanded into six
kernel-visible squared projector traces. -/
theorem target_six_trace_sum (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (htarget : TargetStar c d) :
    let v := htarget.choose
    Complex.normSq (trProj ![c,d] tPX) +
      Complex.normSq (trProj ![c,d] tPY) +
      Complex.normSq (trProj ![c,d] tPZ) +
      Complex.normSq (trProj ![c,d] (tPXv v)) +
      Complex.normSq (trProj ![c,d] (tPYv v)) +
      Complex.normSq (trProj ![c,d] (tPZv v)) = 4 := by
  let v := htarget.choose
  have hA : ∀ i j, starA c v i j = 2 * U c i j :=
    htarget.choose_spec.1
  have rows := target_trace_rows c d hc hd hcode v hA
  rcases scalar_normal_form c d hc hd hnc hnd hcode with
    ⟨hu, hv, hAt, hBt, hdeg, hedge⟩
  have hu' : Complex.normSq (uSpin c 0) + Complex.normSq (uSpin c 1) =
      (1/6 : ℝ) := by
    simpa [uSpin, uMass, spinMass] using hu
  have hv' : Complex.normSq (vSpin d 0) + Complex.normSq (vSpin d 1) =
      (1/6 : ℝ) := by
    simpa [vSpin, vMass, spinMass] using hv
  have hb := SixQubit.Orbit7Spinor.two_spinor_bloch
    (uSpin c 0) (uSpin c 1) (vSpin d 0) (vSpin d 1)
  rw [hu', hv'] at hb
  norm_num at hb
  dsimp only
  rw [rows.1, rows.2.1, rows.2.2.1, rows.2.2.2.1,
    rows.2.2.2.2.1, rows.2.2.2.2.2]
  rw [normSq_six, normSq_neg_six, normSq_six,
    normSq_six, normSq_neg_six, normSq_six]
  linear_combination 36 * hb

/-- A target star forces the raw low-weight enumerator bound, with no purity
or rank hypothesis added to the code assumptions. -/
theorem target_low_bound (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (htarget : TargetStar c d) :
    4 ≤ Aco ![c,d] 1 + Aco ![c,d] 2 := by
  let v := htarget.choose
  have hsum :
      (∑ P ∈ targetPaulis v, Complex.normSq (trProj ![c,d] P)) = 4 := by
    rw [targetPaulis_sum]
    exact target_six_trace_sum c d hc hd hnc hnd hcode htarget
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (targetPaulis_subset v)
    (fun P hlow hnot => Complex.normSq_nonneg (trProj ![c,d] P))
  rw [targetLowPaulis_sum, hsum] at hsub
  exact hsub

/-- Complete one-parameter enumerator certified from the actual target-star
matrix equalities. -/
theorem target_enumerator (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight uniformAv x ≠ 0 -> c x = 0)
    (hd : ∀ x, SS.weight uniformAv x ≠ 2 -> d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (htarget : TargetStar c d) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      SixQubit.Orbit7Family.IsFamilyA ![c,d] a ∧
      SixQubit.Orbit7Family.IsFamilyB ![c,d] a :=
  enumerator_of_low_bound c d hnc hnd hcode
    (target_low_bound c d hc hd hnc hnd hcode htarget)


end

end SixQubit.Orbit7Universal
