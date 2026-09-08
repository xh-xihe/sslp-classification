import SS.HilbertKL

/-!
# The fixed-basis qualification of `thm:finite-projective-group` is essential

`thm:finite-projective-group` restricts to product gates diagonal in the same
local basis in which the `Z_j`-detection conditions are imposed, and the
manuscript's remark says that qualification cannot be dropped.  Its evidence is
a three-qubit example:

  `Q = Span{|+++>, |--->}` satisfies `P Z_j P = 0` for every computational
  basis `Z_j`, while the continuous family `⊗_j exp(i t_j X_j)` preserves `Q`
  and generally induces a nontrivial logical action.

Neither the subspace nor the family existed in this repository, so the remark
had no Lean content and the theorem's "narrower scope" claim was unsupported.
Both are built here.

The family is handled without any exponential.  `rot t` is the matrix of
`exp(i t X)` written out, and the argument needs only how it acts on the two
logical words: `|+>` and `|->` are the `X`-eigenvectors, so each tensor factor
multiplies them by `cos t + i sin t` and `cos t - i sin t`.  The product over
the three qubits therefore scales `|+++>` and `|--->` by two scalars, and at
`t = (pi/2, 0, 0)` those are `i` and `-i`.  They differ, so the induced logical
action is not a scalar.
-/

namespace MainTheory.TransversalFixedBasis

open scoped BigOperators Matrix

noncomputable section

/-! ## The three-qubit code -/

/-- The common amplitude `1/sqrt 8`. -/
noncomputable def amp : ℂ := ((Real.sqrt 8)⁻¹ : ℝ)

/-- The parity mask of all three qubits. -/
def ones3 : SS.BitString 3 := fun _ => true

/-- `(-1)^{|x|}`, the sign carried by `|--->`. -/
def altSign (x : SS.BitString 3) : ℂ := if SS.bdot ones3 x then -1 else 1

/-- `|+++>`, as an amplitude vector. -/
noncomputable def plus3 : SS.State 3 ℂ := fun _ => amp

/-- `|--->`, as an amplitude vector. -/
noncomputable def minus3 : SS.State 3 ℂ := fun x => altSign x * amp

/-- The logical pair spanning `Q`. -/
noncomputable def frame3 : Fin 2 → SS.State 3 ℂ := ![plus3, minus3]

theorem sqrt8_pos : (0 : ℝ) < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)

@[simp] theorem star_amp : star amp = amp := by
  simp [amp]

theorem amp_mul : amp * amp = (8 : ℂ)⁻¹ := by
  have h : ((Real.sqrt 8 : ℝ) : ℂ) * ((Real.sqrt 8 : ℝ) : ℂ) = (8 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 8)]
    norm_num
  simp only [amp, Complex.ofReal_inv]
  rw [← mul_inv, h]

@[simp] theorem star_altSign (x : SS.BitString 3) : star (altSign x) = altSign x := by
  unfold altSign
  by_cases h : SS.bdot ones3 x <;> simp [h]

@[simp] theorem altSign_mul_self (x : SS.BitString 3) : altSign x * altSign x = 1 := by
  unfold altSign
  by_cases h : SS.bdot ones3 x <;> simp [h]

theorem signC_eq (b : Bool) (z : ℂ) : SS.signC b z = (if b then (-1 : ℂ) else 1) * z := by
  cases b <;> simp [SS.signC]

theorem sign_mul_altSign (b : Bool) (t : SS.BitString 3) :
    (if b then (-1 : ℂ) else 1) * altSign t
      = if xor b (SS.bdot ones3 t) then (-1 : ℂ) else 1 := by
  unfold altSign
  cases b <;> by_cases h : SS.bdot ones3 t <;> simp [h]

/-! ## The eight-point counting facts -/

/-- A plus-or-minus-one sum over the cube vanishes when the sign is negative on
exactly half the points. -/
theorem signed_sum_zero (p : SS.BitString 3 → Bool)
    (h : (Finset.univ.filter fun t : SS.BitString 3 => p t = true).card = 4) :
    (∑ t : SS.BitString 3, if p t then (-1 : ℂ) else 1) = 0 := by
  classical
  have hsplit :
      (Finset.univ.filter fun t : SS.BitString 3 => p t = true).card
        + (Finset.univ.filter fun t : SS.BitString 3 => ¬ (p t = true)).card
        = (Finset.univ : Finset (SS.BitString 3)).card :=
    Finset.card_filter_add_card_filter_not _
  have hcard : (Finset.univ : Finset (SS.BitString 3)).card = 8 := by decide
  rw [h, hcard] at hsplit
  have hneg : (Finset.univ.filter fun t : SS.BitString 3 => ¬ (p t = true)).card = 4 := by
    omega
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, h, hneg]
  norm_num

theorem card_coord (j : Fin 3) :
    (Finset.univ.filter fun t : SS.BitString 3 => t j = true).card = 4 := by
  revert j
  decide

theorem card_coord_xor_parity (j : Fin 3) :
    (Finset.univ.filter fun t : SS.BitString 3 =>
      (xor (t j) (SS.bdot ones3 t)) = true).card = 4 := by
  revert j
  decide

theorem card_parity :
    (Finset.univ.filter fun t : SS.BitString 3 => SS.bdot ones3 t = true).card = 4 := by
  decide

/-! ## `Q` is a genuine two-dimensional code -/

theorem card_cube : (Finset.univ : Finset (SS.BitString 3)).card = 8 := by decide

theorem inner_plus_plus : SS.innerC plus3 plus3 = 1 := by
  simp only [SS.innerC, plus3, star_amp]
  rw [Finset.sum_congr rfl fun t _ => amp_mul, Finset.sum_const, card_cube]
  norm_num

theorem inner_minus_minus : SS.innerC minus3 minus3 = 1 := by
  simp only [SS.innerC, minus3, star_mul, star_amp, star_altSign]
  have h : ∀ t : SS.BitString 3,
      amp * altSign t * (altSign t * amp) = (8 : ℂ)⁻¹ := by
    intro t
    rw [← amp_mul]
    linear_combination (amp * amp) * altSign_mul_self t
  rw [Finset.sum_congr rfl fun t _ => h t, Finset.sum_const, card_cube]
  norm_num

theorem inner_plus_minus : SS.innerC plus3 minus3 = 0 := by
  simp only [SS.innerC, plus3, minus3, star_amp]
  have h : ∀ t : SS.BitString 3,
      amp * (altSign t * amp) = (8 : ℂ)⁻¹ * (if SS.bdot ones3 t then (-1 : ℂ) else 1) := by
    intro t
    rw [← amp_mul]
    unfold altSign
    by_cases hp : SS.bdot ones3 t <;> simp [hp]
  rw [Finset.sum_congr rfl fun t _ => h t, ← Finset.mul_sum,
    signed_sum_zero _ card_parity, mul_zero]

/-! ## `Q` detects every computational-basis `Z_j` -/

/-- The Pauli `Z_j`. -/
def Zop (j : Fin 3) : SS.PauliString 3 := ⟨fun _ => false, SS.stdBasis j⟩

@[simp] theorem Zop_numY (j : Fin 3) : (Zop j).numY = 0 := by
  simp [Zop, SS.PauliString.numY]

theorem bdot_stdBasis (j : Fin 3) (t : SS.BitString 3) :
    SS.bdot (SS.stdBasis j) t = t j := by
  revert j t
  decide

theorem pauliAct_Zop (j : Fin 3) (phi : SS.State 3 ℂ) (t : SS.BitString 3) :
    SS.pauliAct (Zop j) phi t = SS.signC (t j) (phi t) := by
  have hx : SS.bxor t (Zop j).x = t := by
    funext i
    simp [SS.bxor, Zop]
  show (Complex.I ^ (Zop j).numY)
      * SS.signC (SS.bdot (Zop j).z (SS.bxor t (Zop j).x)) (phi (SS.bxor t (Zop j).x)) = _
  rw [hx, Zop_numY]
  simp [Zop, bdot_stdBasis]

/-- **`P Z_j P = 0`.**  Every matrix element of a computational-basis `Z_j`
between the two logical words vanishes, so `Q` detects each of them with the
scalar `0`. -/
theorem kl_Zop (j : Fin 3) : SS.KLCondition frame3 (Zop j) := by
  classical
  have hpp : ∀ t : SS.BitString 3,
      star (plus3 t) * SS.signC (t j) (plus3 t)
        = (8 : ℂ)⁻¹ * (if t j then (-1 : ℂ) else 1) := by
    intro t
    rw [signC_eq]
    simp only [plus3, star_amp]
    rw [← amp_mul]
    ring
  have hmm : ∀ t : SS.BitString 3,
      star (minus3 t) * SS.signC (t j) (minus3 t)
        = (8 : ℂ)⁻¹ * (if t j then (-1 : ℂ) else 1) := by
    intro t
    rw [signC_eq]
    simp only [minus3, star_mul, star_amp, star_altSign]
    rw [← amp_mul]
    linear_combination
      (amp * amp * (if t j then (-1 : ℂ) else 1)) * altSign_mul_self t
  have hpm : ∀ t : SS.BitString 3,
      star (plus3 t) * SS.signC (t j) (minus3 t)
        = (8 : ℂ)⁻¹ * (if xor (t j) (SS.bdot ones3 t) then (-1 : ℂ) else 1) := by
    intro t
    rw [signC_eq, ← sign_mul_altSign]
    simp only [plus3, minus3, star_amp]
    rw [← amp_mul]
    ring
  have hmp : ∀ t : SS.BitString 3,
      star (minus3 t) * SS.signC (t j) (plus3 t)
        = (8 : ℂ)⁻¹ * (if xor (t j) (SS.bdot ones3 t) then (-1 : ℂ) else 1) := by
    intro t
    rw [signC_eq, ← sign_mul_altSign]
    simp only [plus3, minus3, star_mul, star_amp, star_altSign]
    rw [← amp_mul]
    ring
  refine ⟨0, fun a b => ?_⟩
  simp only [SS.innerC, pauliAct_Zop, ite_self]
  fin_cases a <;> fin_cases b <;>
    simp only [frame3, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  · rw [Finset.sum_congr rfl fun t _ => hpp t, ← Finset.mul_sum,
      signed_sum_zero _ (card_coord j), mul_zero]
  · rw [Finset.sum_congr rfl fun t _ => hpm t, ← Finset.mul_sum,
      signed_sum_zero _ (card_coord_xor_parity j), mul_zero]
  · rw [Finset.sum_congr rfl fun t _ => hmp t, ← Finset.mul_sum,
      signed_sum_zero _ (card_coord_xor_parity j), mul_zero]
  · rw [Finset.sum_congr rfl fun t _ => hmm t, ← Finset.mul_sum,
      signed_sum_zero _ (card_coord j), mul_zero]

/-! ## The transversal family in the local `X` basis -/

/-- Bool as a matrix index. -/
def bitIdx (b : Bool) : Fin 2 := if b then 1 else 0

/-- The matrix `[[c, i s], [i s, c]]`; at `c = cos t`, `s = sin t` this is
`exp(i t X)`. -/
noncomputable def rotOf (c s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![c, Complex.I * s; Complex.I * s, c]

/-- The matrix of `exp(i t X)`. -/
noncomputable def rot (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  rotOf (Real.cos t) (Real.sin t)

theorem cos_sq_add_sin_sq (t : ℝ) :
    ((Real.cos t : ℂ)) ^ 2 + ((Real.sin t : ℂ)) ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq t
  have hc : ((Real.cos t ^ 2 + Real.sin t ^ 2 : ℝ) : ℂ) = 1 := by
    rw [add_comm, h]
    norm_num
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add]
  exact hc

/-- `rotOf c s` is unitary whenever `c` and `s` are real with `c^2 + s^2 = 1`. -/
theorem rotOf_unitary {c s : ℂ} (hc : star c = c) (hs : star s = s)
    (h : c ^ 2 + s ^ 2 = 1) : rotOf c s * (rotOf c s)ᴴ = 1 := by
  have hI : star Complex.I = -Complex.I := by simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [rotOf, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.one_apply, star_mul, hI, hc, hs,
      Fin.zero_eta, Fin.mk_one]
  · simp only [if_true]
    linear_combination h - s ^ 2 * Complex.I_sq
  · norm_num
    ring
  · norm_num
    ring
  · simp only [if_true]
    linear_combination h - s ^ 2 * Complex.I_sq

theorem rot_unitary (t : ℝ) : rot t * (rot t)ᴴ = 1 :=
  rotOf_unitary (by simp only [RCLike.star_def, Complex.conj_ofReal])
    (by simp only [RCLike.star_def, Complex.conj_ofReal]) (cos_sq_add_sin_sq t)

/-- The transversal product gate acting on amplitude vectors. -/
noncomputable def localAct (U : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (phi : SS.State 3 ℂ) : SS.State 3 ℂ :=
  fun x => ∑ y : SS.BitString 3, (∏ j, U j (bitIdx (x j)) (bitIdx (y j))) * phi y

/-- A product gate applied to a product state factorizes. -/
theorem localAct_prod (U : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (f : Fin 3 → Bool → ℂ) (x : SS.BitString 3) :
    (∑ y : SS.BitString 3, (∏ j, U j (bitIdx (x j)) (bitIdx (y j))) * (∏ j, f j (y j)))
      = ∏ j, (∑ b : Bool, U j (bitIdx (x j)) (bitIdx b) * f j b) := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun y _ => (Finset.prod_mul_distrib).symm

theorem altSign_prod (y : SS.BitString 3) :
    altSign y = ∏ j : Fin 3, (if y j then (-1 : ℂ) else 1) := by
  have hb : SS.bdot ones3 y = xor (y 0) (xor (y 1) (y 2)) := by
    revert y
    decide
  rw [Fin.prod_univ_three, altSign, hb]
  cases h0 : y 0 <;> cases h1 : y 1 <;> cases h2 : y 2 <;> norm_num

theorem rot_row_sum (s : ℝ) (c : Bool) :
    (∑ b : Bool, rot s (bitIdx c) (bitIdx b))
      = (Real.cos s : ℂ) + Complex.I * (Real.sin s : ℂ) := by
  cases c <;> simp [rot, rotOf, bitIdx]
  ring

theorem rot_row_sum_signed (s : ℝ) (c : Bool) :
    (∑ b : Bool, rot s (bitIdx c) (bitIdx b) * (if b then (-1 : ℂ) else 1))
      = (if c then (-1 : ℂ) else 1)
        * ((Real.cos s : ℂ) - Complex.I * (Real.sin s : ℂ)) := by
  cases c <;> simp [rot, rotOf, bitIdx] <;> ring

/-- **The family preserves `|+++>`**, scaling it by `∏ (cos t_j + i sin t_j)`. -/
theorem localAct_plus3 (t : Fin 3 → ℝ) (x : SS.BitString 3) :
    localAct (fun j => rot (t j)) plus3 x
      = (∏ j, ((Real.cos (t j) : ℂ) + Complex.I * (Real.sin (t j) : ℂ))) * plus3 x := by
  classical
  have key := localAct_prod (fun j => rot (t j)) (fun _ _ => (1 : ℂ)) x
  simp only [Finset.prod_const_one, mul_one] at key
  simp only [localAct, plus3]
  rw [← Finset.sum_mul, key,
    Finset.prod_congr rfl fun j _ => rot_row_sum (t j) (x j)]

/-- **The family preserves `|--->`**, scaling it by `∏ (cos t_j - i sin t_j)`. -/
theorem localAct_minus3 (t : Fin 3 → ℝ) (x : SS.BitString 3) :
    localAct (fun j => rot (t j)) minus3 x
      = (∏ j, ((Real.cos (t j) : ℂ) - Complex.I * (Real.sin (t j) : ℂ))) * minus3 x := by
  classical
  have key := localAct_prod (fun j => rot (t j))
    (fun _ b => (if b then (-1 : ℂ) else 1)) x
  have hstep : ∀ y : SS.BitString 3,
      (∏ j, rot (t j) (bitIdx (x j)) (bitIdx (y j))) * (altSign y * amp)
        = ((∏ j, rot (t j) (bitIdx (x j)) (bitIdx (y j)))
            * (∏ j, (if y j then (-1 : ℂ) else 1))) * amp := by
    intro y
    rw [altSign_prod]
    ring
  simp only [localAct, minus3]
  rw [Finset.sum_congr rfl fun y _ => hstep y, ← Finset.sum_mul, key,
    Finset.prod_congr rfl fun j _ => rot_row_sum_signed (t j) (x j),
    Finset.prod_mul_distrib, ← altSign_prod]
  ring

/-! ## The counterexample -/

theorem I_ne_neg_I : (Complex.I : ℂ) ≠ -Complex.I := by
  intro h
  have : (2 : ℂ) * Complex.I = 0 := by linear_combination h
  simp [Complex.I_ne_zero] at this

/-- **The manuscript's counterexample.**

`Q = Span{|+++>, |--->}` detects every computational-basis `Z_j` with the
scalar `0`, and the transversal family `⊗_j exp(i t_j X_j)` -- which is
diagonal in the local `X` basis, not the basis of the detection conditions --
preserves `Q` while scaling the two logical words by different factors.  So it
acts nontrivially on the logical space, and the fixed-basis qualification of
`thm:finite-projective-group` cannot be dropped. -/
theorem fixed_basis_essential :
    SS.innerC plus3 plus3 = 1 ∧ SS.innerC minus3 minus3 = 1 ∧
      SS.innerC plus3 minus3 = 0 ∧
      (∀ j : Fin 3, SS.KLCondition frame3 (Zop j)) ∧
      ∃ t : Fin 3 → ℝ, ∃ lam mu : ℂ,
        (∀ x, localAct (fun j => rot (t j)) plus3 x = lam * plus3 x) ∧
        (∀ x, localAct (fun j => rot (t j)) minus3 x = mu * minus3 x) ∧
        lam ≠ mu := by
  refine ⟨inner_plus_plus, inner_minus_minus, inner_plus_minus, kl_Zop,
    ![Real.pi / 2, 0, 0], Complex.I, -Complex.I, ?_, ?_, I_ne_neg_I⟩
  · intro x
    have h := localAct_plus3 ![Real.pi / 2, 0, 0] x
    rw [h]
    congr 1
    rw [Fin.prod_univ_three]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  · intro x
    have h := localAct_minus3 ![Real.pi / 2, 0, 0] x
    rw [h]
    congr 1
    rw [Fin.prod_univ_three]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

end

end MainTheory.TransversalFixedBasis
