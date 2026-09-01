import MainTheory.BoundedRepresentation
import MainTheory.LocalPhaseConjugation

/-!
# Labelled gates are closed under the conjugation

The transport carries a symmetry of the normalized code to `flipPhase u x0` on
the original.  For `HasBoundedRepresentation` that flipped symmetry has to be
the gate of a bounded label again, not merely some local phase.  It is: the flip
inverts the phase at the flipped sites, and inverting `zeta^a` is `zeta^(-a)`,
which is the gate of the label with the angle negated in `ZMod (q+1)`.

Also here: the label whose gate is the identity, which is what represents the
projectively trivial class.
-/

namespace MainTheory.LabelledGates

variable {n d : ℕ}

open MainTheory.ClassificationLevels
open MainTheory.BoundedRepresentation
open MainTheory.LocalPhaseConjugation
open MainTheory.ProjectiveGroupFinite

/-! ## Arithmetic of `circlePhase` -/

theorem circlePhase_inv (t : ℝ) : (circlePhase t)⁻¹ = circlePhase (-t) := by
  refine Subtype.ext ?_
  show star (Complex.exp ((t : ℂ) * Complex.I))
      = Complex.exp (((-t : ℝ) : ℂ) * Complex.I)
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  push_cast
  simp [Complex.conj_I]

/-- `circlePhase` has period `2 pi`, which is what lets a negated angle be read
as the complementary residue. -/
theorem circlePhase_add_two_pi (t : ℝ) :
    circlePhase (t + 2 * Real.pi) = circlePhase t := by
  refine Subtype.ext ?_
  simp only [circlePhase]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-! ## Negating a residue -/

/-- The angle of the negated residue, read back through `ZMod`. -/
theorem circlePhase_neg_residue (q : ℕ) (hq : 0 < q) (a : ZMod q) :
    circlePhase (2 * Real.pi * (((-a).val : ℕ) : ℝ) / (q : ℝ))
      = (circlePhase (2 * Real.pi * ((a.val : ℕ) : ℝ) / (q : ℝ)))⁻¹ := by
  haveI : NeZero q := ⟨hq.ne'⟩
  rw [circlePhase_inv]
  by_cases ha : a = 0
  · subst ha
    simp
  · have hval : ((-a).val : ℕ) = q - a.val := by
      rw [ZMod.neg_val, if_neg ha]
    rw [hval]
    have hlt : a.val < q := ZMod.val_lt a
    have hqR : ((q : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
    have hcast : (((q - a.val : ℕ)) : ℝ) = (q : ℝ) - (a.val : ℝ) := by
      push_cast [Nat.cast_sub hlt.le]
      ring
    rw [hcast]
    have hsplit : 2 * Real.pi * ((q : ℝ) - (a.val : ℝ)) / (q : ℝ)
        = -(2 * Real.pi * (a.val : ℝ) / (q : ℝ)) + 2 * Real.pi := by
      field_simp
      ring
    rw [hsplit, circlePhase_add_two_pi]

/-! ## The label set is closed under the conjugation -/

/-- Negating the angle vector at the flipped sites, inside the label. -/
def flipLabel (lbl : BoundedPhaseLabel n B) (x0 : SS.BitString n) :
    BoundedPhaseLabel n B :=
  ⟨lbl.1, fun j => if x0 j then -(lbl.2 j) else lbl.2 j⟩

/-- **`flipPhase` of a labelled gate is a labelled gate.**

This is what keeps `HasBoundedRepresentation` in range after the transport: the
symmetry it hands back is still named by a bounded label. -/
theorem flipPhase_gateOfLabel (lbl : BoundedPhaseLabel n B) (x0 : SS.BitString n) :
    flipPhase (gateOfLabel lbl) x0 = gateOfLabel (flipLabel lbl x0) := by
  funext j
  have hq : 0 < lbl.1.val + 1 := Nat.succ_pos _
  by_cases hx : x0 j
  · simp only [flipPhase, hx, if_true, gateOfLabel, flipLabel]
    have h := circlePhase_neg_residue (lbl.1.val + 1) hq (lbl.2 j)
    push_cast at h
    rw [← h]
  · simp [flipPhase, hx, gateOfLabel, flipLabel]

/-- The label whose gate is the identity: modulus one, all angles zero.  This
represents the projectively trivial class. -/
def trivialLabel (hB : 0 < B) : BoundedPhaseLabel n B :=
  ⟨⟨0, hB⟩, fun _ => 0⟩

@[simp] theorem gateOfLabel_trivial (hB : 0 < B) :
    gateOfLabel (n := n) (trivialLabel hB) = 1 := by
  funext j
  refine Subtype.ext ?_
  simp [gateOfLabel, trivialLabel, circlePhase]

/-! ## Recognising a labelled gate

`HasBoundedRepresentation` needs a *label* for a symmetry, and the entrance
supplies a bound on the order rather than a label.  The bridge is this: a local
phase whose entries are `q`-th roots of unity for some `q <= 9` is the gate of a
label, because the canonical primitive root generates all of them.

Stating it this way avoids reconciling the resolution's arbitrary primitive root
with the canonical one -- only the order matters, not which root was chosen. -/

/-- The canonical primitive `q`-th root of unity. -/
noncomputable def canonicalRoot (q : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (q : ℂ))

theorem circlePhase_eq_canonicalRoot_pow (q a : ℕ) (hq : 0 < q) :
    ((circlePhase (2 * Real.pi * (a : ℝ) / (q : ℝ)) : unitary ℂ) : ℂ)
      = canonicalRoot q ^ a := by
  rw [circlePhase, canonicalRoot, ← Complex.exp_nat_mul]
  have hqne : ((q : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  push_cast
  field_simp

theorem canonicalRoot_isPrimitiveRoot (q : ℕ) (hq : 0 < q) :
    IsPrimitiveRoot (canonicalRoot q) q := by
  have := Complex.isPrimitiveRoot_exp q hq.ne'
  simpa [canonicalRoot, mul_comm, mul_assoc, mul_left_comm] using this

/-- **A local phase whose order fits under the label bound is a labelled
gate.**  At `B = 9` this is the paper's "order at most nine". -/
theorem exists_label_of_pow_eq_one (m : ℕ) (hm : m < B)
    (u : LocalPhase n) (h : ∀ j, ((u j : ℂ)) ^ (m + 1) = 1) :
    ∃ lbl : BoundedPhaseLabel n B, gateOfLabel lbl = u := by
  have hq : 0 < m + 1 := Nat.succ_pos m
  haveI : NeZero (m + 1) := ⟨hq.ne'⟩
  have hroot := canonicalRoot_isPrimitiveRoot (m + 1) hq
  choose a ha hpow using fun j => hroot.eq_pow_of_pow_eq_one (h j)
  refine ⟨⟨⟨m, hm⟩, fun j => (a j : ZMod (m + 1))⟩, ?_⟩
  funext j
  refine Subtype.ext ?_
  simp only [gateOfLabel]
  have hval : ((a j : ZMod (m + 1))).val = a j := ZMod.val_natCast_of_lt (ha j)
  rw [hval]
  have hcast : ((↑(⟨m, hm⟩ : Fin B) : ℝ)) + 1 = ((m + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hcast, circlePhase_eq_canonicalRoot_pow (m + 1) (a j) hq, hpow j]

end MainTheory.LabelledGates
