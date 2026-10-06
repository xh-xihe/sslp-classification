import MainTheory.LabelledGates
import MainTheory.RankTwoGlobal
import MainTheory.BoundedRepresentation
import MainTheory.LocalPhaseConjugation
import MainTheory.Normalize

/-!
# The finite gate as a local phase

The entrance works with `Module.End` objects built from `Gate.gate`, while the
transport of `MainTheory/IntrinsicTransport.lean` works with `LocalPhase`.  This
file connects the two, which is the last structural bridge Section II needs.

A finite gate `D(a;q)` for a root of unity `zeta` is the diagonal action of the
local phase whose site `j` carries `zeta ^ a j`.  The identity is the same
periodicity argument used elsewhere: the subset-sum residue and the plain sum of
the site residues differ by a multiple of `q`, which `zeta` does not see.
-/

namespace MainTheory.FiniteGateAsPhase

open MainTheory.ClassificationLevels
open MainTheory.LabelledGates

variable {n q : ℕ} [NeZero q]

/-- A power of a root of unity, as a unitary. -/
noncomputable def rootPower (zeta : ℂ) (hz : zeta ^ q = 1) (k : ℕ) : unitary ℂ :=
  ⟨zeta ^ k, by
    have hnorm : ‖zeta‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz (NeZero.ne q)
    have hk : ‖(zeta ^ k)‖ = 1 := by
      rw [norm_pow, hnorm, one_pow]
    have hns : Complex.normSq (zeta ^ k) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hk, one_pow]
    constructor
    · rw [Complex.star_def]
      have := Complex.mul_conj (zeta ^ k)
      rw [mul_comm] at this
      rw [this, hns]
      norm_num
    · rw [Complex.star_def, Complex.mul_conj, hns]
      norm_num ⟩

@[simp] theorem coe_rootPower (zeta : ℂ) (hz : zeta ^ q = 1) (k : ℕ) :
    ((rootPower zeta hz k : unitary ℂ) : ℂ) = zeta ^ k := rfl

/-- The local phase of a finite angle vector. -/
noncomputable def phaseOfAngle (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) : LocalPhase n :=
  fun j => rootPower zeta hz (a j).val

/-! ## The identity -/

omit [NeZero q] in
/-- Powers of `zeta` only see the exponent modulo `q`. -/
theorem zeta_pow_mod (zeta : ℂ) (hz : zeta ^ q = 1) (k : ℕ) :
    zeta ^ (k % q) = zeta ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k q]
  rw [pow_add, pow_mul, hz, one_pow, one_mul]

/-- **The finite gate is the diagonal action of its local phase.** -/
theorem diagonalValue_phaseOfAngle (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) (s : SS.BitString n) :
    diagonalValue (phaseOfAngle zeta hz a) s
      = zeta ^ (SS.weight a s).val := by
  classical
  rw [diagonalValue]
  have hprod : (∏ j, if s j then ((phaseOfAngle zeta hz a j : unitary ℂ) : ℂ) else 1)
      = zeta ^ (∑ j, if s j then (a j).val else 0) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases h : s j
    · simp [h, phaseOfAngle]
    · simp [h]
  rw [hprod]
  refine (zeta_pow_mod zeta hz _).symm.trans ?_
  congr 1
  have hsum : SS.weight a s = ((∑ j, if s j then (a j).val else 0 : ℕ) : ZMod q) := by
    rw [SS.weight]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : s j
    · simp [h, SS.bit, ZMod.natCast_val, ZMod.cast_id]
    · simp [h, SS.bit]
  rw [hsum, ZMod.val_natCast]

/-- The gate itself, as a map on states. -/
theorem gate_eq_diagonalAction (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) (psi : SS.State n ℂ) :
    Gate.gate zeta a psi = diagonalAction (phaseOfAngle zeta hz a) psi := by
  funext s
  rw [Gate.gate, Gate.diag, diagonalAction, diagonalValue_phaseOfAngle]

/-! ## Any bounded finite gate is labelled

`LabelledGates.exists_label_of_pow_eq_one` asks for a local phase whose entries
have order dividing `m + 1`.  Every finite gate for an `(m+1)`-st root of unity
has that property automatically -- its site `j` carries `zeta ^ a j`, and
`(zeta ^ a j) ^ (m+1) = (zeta ^ (m+1)) ^ a j = 1`.  So the bound the entrance
produces on the order is by itself enough to name the gate by a label; nothing
about which root, or which angle vector, has to be tracked. -/

theorem exists_label_of_phaseOfAngle (m : ℕ) (hm : m < B) (zeta : ℂ)
    (hz : zeta ^ (m + 1) = 1) (a : Fin n → ZMod (m + 1)) :
    ∃ lbl : ProjectiveGroupFinite.BoundedPhaseLabel n B,
      BoundedRepresentation.gateOfLabel lbl = phaseOfAngle zeta hz a := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  refine LabelledGates.exists_label_of_pow_eq_one m hm _ (fun j => ?_)
  rw [phaseOfAngle, coe_rootPower, ← pow_mul, mul_comm, pow_mul, hz, one_pow]

/-- The same statement keyed on the modulus rather than its predecessor.  The
entrance bounds the fresh order directly, so this is the form actually used. -/
theorem exists_label_of_phaseOfAngle_le (hq : q ≤ B) (zeta : ℂ)
    (hz : zeta ^ q = 1) (a : Fin n → ZMod q) :
    ∃ lbl : ProjectiveGroupFinite.BoundedPhaseLabel n B,
      BoundedRepresentation.gateOfLabel lbl = phaseOfAngle zeta hz a := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 :=
    ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne q))).symm⟩
  exact exists_label_of_phaseOfAngle m (by omega) zeta hz a

/-! ## Flipping and scaling the angle

`SixQubitSemanticEntrance.normalizedFiniteAngle` is
`fun j => T.unit * Normalize.flip G.angle T.x0 j`, so the normalization the
entrance performs is exactly a flip followed by a unit scaling.  Both operations
are visible on the local phase: the flip is `LocalPhaseConjugation.flipPhase`,
and the scaling is a power. -/

/-- A root of unity at the negated residue is the inverse. -/
theorem rootPow_neg_residue (zeta : ℂ) (hz : zeta ^ q = 1) (a : ZMod q) :
    zeta ^ ((-a).val) = (zeta ^ (a.val))⁻¹ := by
  have hne : zeta ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne q)] at hz
    exact zero_ne_one hz
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add]
  by_cases ha : a = 0
  · subst ha
    simp
  · have hsum : (-a).val + a.val = q := by
      rw [ZMod.neg_val, if_neg ha]
      have := ZMod.val_lt a
      omega
    rw [hsum, hz]

/-- **The flip on local phases is the flip on angle vectors.** -/
theorem flipPhase_phaseOfAngle (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) (x0 : SS.BitString n) :
    LocalPhaseConjugation.flipPhase (phaseOfAngle zeta hz a) x0
      = phaseOfAngle zeta hz (MainTheory.Normalize.flip a x0) := by
  funext j
  refine Subtype.ext ?_
  by_cases hx : x0 j
  · simp only [LocalPhaseConjugation.flipPhase, hx, if_true, phaseOfAngle,
      MainTheory.Normalize.flip]
    have h1 : ((rootPower zeta hz (a j).val : unitary ℂ) : ℂ)
        * (((rootPower zeta hz (a j).val)⁻¹ : unitary ℂ) : ℂ) = 1 :=
      LocalPhaseConjugation.coe_mul_coe_inv _
    rw [coe_rootPower] at h1
    have h2 : (((rootPower zeta hz (a j).val)⁻¹ : unitary ℂ) : ℂ)
        = (zeta ^ (a j).val)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [mul_comm]
      exact h1
    rw [h2, coe_rootPower, rootPow_neg_residue zeta hz (a j)]
  · simp [LocalPhaseConjugation.flipPhase, hx, phaseOfAngle,
      MainTheory.Normalize.flip]

/-- **Scaling the angle is taking a power.**

The other half of `normalizedFiniteAngle`: multiplying the angle vector by a
unit of `ZMod q` raises the gate to that power. -/
theorem phaseOfAngle_natMul (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) (c : ℕ) :
    phaseOfAngle zeta hz (fun j => (c : ZMod q) * a j)
      = fun j => (phaseOfAngle zeta hz a j) ^ c := by
  funext j
  refine Subtype.ext ?_
  simp only [phaseOfAngle, coe_rootPower, SubmonoidClass.coe_pow]
  rw [← pow_mul, ← zeta_pow_mod zeta hz ((a j).val * c)]
  congr 1
  have hcast : ((c : ZMod q) * a j) = (((c * (a j).val : ℕ)) : ZMod q) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [hcast, ZMod.val_natCast, mul_comm]


/-- **A finite phase has order dividing its modulus.**

Every site is a power of `zeta`, so the `q`-th power of the whole local phase
is the identity.  This supplies the period hypothesis of
`BoundedClassPower.BoundedClass.of_pow_coprime`. -/
theorem phaseOfAngle_pow_eq_one (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) : (phaseOfAngle zeta hz a) ^ q = 1 := by
  funext j
  refine Subtype.ext ?_
  have : ((phaseOfAngle zeta hz a j : unitary ℂ) : ℂ) ^ q = 1 := by
    rw [phaseOfAngle, coe_rootPower, ← pow_mul, mul_comm, pow_mul, hz, one_pow]
  simpa [Pi.pow_apply, SubmonoidClass.coe_pow] using this

end MainTheory.FiniteGateAsPhase
