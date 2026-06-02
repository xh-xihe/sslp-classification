import DyadicLifts.KL

/-!
# Bell parity flags and the Bell-pair Pauli table

This module formalizes `dyadic_theorem_lean.tex`, Section 3:

* `Definition (Bell parity flags)` — `|φ⟩`, `|ψ⟩`, and `Φ_p`.
* `Lemma (Bell-pair Pauli matrix elements)` — the full 16-case two-qubit Pauli
  table inside `span{|φ⟩,|ψ⟩}`.

The flags are orthonormal; this orthonormality is what makes the dyadic lift an
isometry.  All matrix elements `⟨Φ_p|B|Φ_q⟩` are reduced to finite complex
arithmetic via `mel_bflag_eq`.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

/-! ## The scalar `1/√2` -/

/-- The real scalar `1/√2`, as a complex number. -/
noncomputable def isqrt2 : ℂ := (Real.sqrt 2)⁻¹

@[simp] lemma conj_isqrt2 : conj isqrt2 = isqrt2 := by
  rw [isqrt2, ← Complex.ofReal_inv, Complex.conj_ofReal]

lemma isqrt2_mul_self : isqrt2 * isqrt2 = 1 / 2 := by
  rw [isqrt2, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  rw [← mul_inv]
  rw [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- Collect a doubly-scaled Bell sum: `(1/√2)·((1/√2)A + (1/√2)B) = (A+B)/2`. -/
lemma isqrt2_collect (A B : ℂ) : isqrt2 * (isqrt2 * A + isqrt2 * B) = (1 / 2) * (A + B) := by
  rw [mul_add, ← mul_assoc, ← mul_assoc]
  simp only [isqrt2_mul_self]
  ring

/-! ## The Bell flags -/

/-- First basis string of the parity-`p` Bell flag. -/
def bket1 : Bool → BitString 2
  | false => ![false, false]
  | true  => ![false, true]

/-- Second basis string of the parity-`p` Bell flag. -/
def bket2 : Bool → BitString 2
  | false => ![true, true]
  | true  => ![true, false]

/-- The parity-`p` Bell flag `Φ_p = (|·0·⟩ + |·1·⟩)/√2` (even parity = `φ`,
odd parity = `ψ`). -/
noncomputable def bflag (p : Bool) : Hil 2 := isqrt2 • (ket (bket1 p) + ket (bket2 p))

/-- `|φ⟩ = (|00⟩ + |11⟩)/√2`. -/
noncomputable def bphi : Hil 2 := bflag false
/-- `|ψ⟩ = (|01⟩ + |10⟩)/√2`. -/
noncomputable def bpsi : Hil 2 := bflag true

/-! ## Orthonormality of the Bell flags -/

/-- **The Bell flags are orthonormal:** `⟨Φ_p|Φ_q⟩ = δ_{pq}`. -/
@[simp] lemma inn_bflag (p q : Bool) : ⟪bflag p, bflag q⟫ = if p = q then 1 else 0 := by
  cases p <;> cases q <;>
  · simp only [bflag, bket1, bket2, inn_smul_left, inn_smul_right, inn_add_left,
      inn_add_right, inn_ket_ket, conj_isqrt2]
    rw [isqrt2_collect]
    norm_num [funext_iff, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]

@[simp] lemma inn_bphi_bphi : ⟪bphi, bphi⟫ = 1 := by simp [bphi]
@[simp] lemma inn_bpsi_bpsi : ⟪bpsi, bpsi⟫ = 1 := by simp [bpsi]
@[simp] lemma inn_bphi_bpsi : ⟪bphi, bpsi⟫ = 0 := by simp [bphi, bpsi]
@[simp] lemma inn_bpsi_bphi : ⟪bpsi, bphi⟫ = 0 := by simp [bphi, bpsi]

/-! ## Reduction of Bell matrix elements -/

/-- The action of a Pauli on a basis ket is the corresponding matrix-element column. -/
lemma papply_ket (B : Fin 2 → SQ) (t : BitString 2) :
    papply B (ket t) = fun s => pauliME B s t := by
  funext s
  simp only [papply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro u _ hu; simp [ket_apply, hu]
  · intro h; exact absurd (Finset.mem_univ t) h

/-- Matrix element between basis kets is the Pauli matrix element. -/
lemma mel_ket_ket (r t : BitString 2) (B : Fin 2 → SQ) :
    mel (ket r) B (ket t) = pauliME B r t := by
  rw [mel, papply_ket, inn_ket_left]

/-- Two-qubit Pauli matrix element splits into its two single-qubit factors. -/
lemma pauliME_two (P Q : SQ) (s t : BitString 2) :
    pauliME ![P, Q] s t = sqME P (s 0) (t 0) * sqME Q (s 1) (t 1) := by
  simp [pauliME, Fin.prod_univ_two]

/-- **The Bell matrix element as a 4-term complex sum.** -/
lemma mel_bflag_eq (p q : Bool) (B : Fin 2 → SQ) :
    mel (bflag p) B (bflag q)
      = (1 / 2 : ℂ) * (pauliME B (bket1 p) (bket1 q) + pauliME B (bket1 p) (bket2 q)
            + pauliME B (bket2 p) (bket1 q) + pauliME B (bket2 p) (bket2 q)) := by
  unfold bflag
  simp only [mel_smul_left, mel_smul_right, mel_add_left, mel_add_right, mel_ket_ket,
    conj_isqrt2]
  rw [isqrt2_collect]
  ring

/-! ## The Bell-pair Pauli table (Lemma: Bell-pair Pauli matrix elements)

These are the entries the distance-`3` propagation actually uses, computed
directly from `mel_bflag_eq`.  We use the convention `Φ₀ = φ` (even, `p = false`),
`Φ₁ = ψ` (odd, `p = true`). -/

/-- `B = II`: `(φφ,ψψ,φψ,ψφ) = (1,1,0,0)`. -/
lemma mel_II (p q : Bool) :
    mel (bflag p) ![SQ.I, SQ.I] (bflag q) = if p = q then 1 else 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = XX`: `(1,1,0,0)`. -/
lemma mel_XX (p q : Bool) :
    mel (bflag p) ![SQ.X, SQ.X] (bflag q) = if p = q then 1 else 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = ZZ`: `(1,-1,0,0)`. -/
lemma mel_ZZ (p q : Bool) :
    mel (bflag p) ![SQ.Z, SQ.Z] (bflag q) = if p = q then (if p then -1 else 1) else 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = YY`: `(-1,1,0,0)`. -/
lemma mel_YY (p q : Bool) :
    mel (bflag p) ![SQ.Y, SQ.Y] (bflag q) = if p = q then (if p then 1 else -1) else 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = IX`: `(0,0,1,1)`. -/
lemma mel_IX (p q : Bool) :
    mel (bflag p) ![SQ.I, SQ.X] (bflag q) = if p = q then 0 else 1 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = XI`: `(0,0,1,1)`. -/
lemma mel_XI (p q : Bool) :
    mel (bflag p) ![SQ.X, SQ.I] (bflag q) = if p = q then 0 else 1 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = YZ`: `(0,0,-i,i)`. -/
lemma mel_YZ (p q : Bool) :
    mel (bflag p) ![SQ.Y, SQ.Z] (bflag q) =
      if p = q then 0 else (if p then Complex.I else -Complex.I) := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = ZY`: `(0,0,-i,i)`. -/
lemma mel_ZY (p q : Bool) :
    mel (bflag p) ![SQ.Z, SQ.Y] (bflag q) =
      if p = q then 0 else (if p then Complex.I else -Complex.I) := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-! The remaining eight two-qubit Paulis have **no** overlap inside `span{φ,ψ}`
(`(0,0,0,0)` row of the table). -/

/-- `B = IY`: all overlaps vanish. -/
lemma mel_IY (p q : Bool) : mel (bflag p) ![SQ.I, SQ.Y] (bflag q) = 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = YI`: all overlaps vanish. -/
lemma mel_YI (p q : Bool) : mel (bflag p) ![SQ.Y, SQ.I] (bflag q) = 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = IZ`: all overlaps vanish. -/
lemma mel_IZ (p q : Bool) : mel (bflag p) ![SQ.I, SQ.Z] (bflag q) = 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = ZI`: all overlaps vanish. -/
lemma mel_ZI (p q : Bool) : mel (bflag p) ![SQ.Z, SQ.I] (bflag q) = 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = XY`: all overlaps vanish. -/
lemma mel_XY (p q : Bool) : mel (bflag p) ![SQ.X, SQ.Y] (bflag q) = 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = YX`: all overlaps vanish. -/
lemma mel_YX (p q : Bool) : mel (bflag p) ![SQ.Y, SQ.X] (bflag q) = 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = XZ`: all overlaps vanish. -/
lemma mel_XZ (p q : Bool) : mel (bflag p) ![SQ.X, SQ.Z] (bflag q) = 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

/-- `B = ZX`: all overlaps vanish. -/
lemma mel_ZX (p q : Bool) : mel (bflag p) ![SQ.Z, SQ.X] (bflag q) = 0 := by
  cases p <;> cases q <;>
  · rw [mel_bflag_eq]
    simp only [bket1, bket2, pauliME_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, sqME_I, sqME_X, sqME_Y, sqME_Z]
    norm_num [Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im]

end DyadicLifts
