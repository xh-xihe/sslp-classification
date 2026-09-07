import MainTheory.BooleanCubeConnectivity
import SS.Pauli
import MainTheory.ParityFourMomentMatrix

/-!
The exact parity-four moment cross-polytope.  The moment equations quantify all
Walsh masks of weight at most two on the complete even and odd parity classes.
-/

namespace MainTheory.ParityFour

open scoped BigOperators

noncomputable section

abbrev Cube := SS.BitString 4

def point (k : Fin 16) : Cube := fun i => k.val.testBit i.val

def pointEquiv : Fin 16 ≃ Cube := Equiv.ofBijective point (by decide)

@[simp] theorem pointEquiv_apply (k : Fin 16) : pointEquiv k = point k := rfl

theorem point_apply (k : Fin 16) (i : Fin 4) : point k i = k.val.testBit i.val := rfl

def parity (x : Cube) : Bool := SS.bdot (fun _ => true) x

theorem parity_point (k : Fin 16) : parity (point k) =
    ![false, true, true, false, true, false, false, true,
      true, false, false, true, false, true, true, false] k := by
  revert k
  decide

def character (z x : Cube) : ℝ := if SS.bdot z x then -1 else 1

def moment (p : Cube → ℝ) (b : Bool) (z : Cube) : ℝ :=
  ∑ x, if parity x = b then p x * character z x else 0

def mass (p : Cube → ℝ) (b : Bool) : ℝ :=
  ∑ x, if parity x = b then p x else 0

def MomentEquations (p : Cube → ℝ) : Prop :=
  mass p false = 1 ∧ mass p true = 1 ∧
    ∀ z : Cube, SS.hammingWt z ≤ 2 → moment p false z = moment p true z

def probability (a : Fin 4 → ℝ) (x : Cube) : ℝ :=
  (1 + ∑ i, a i * BooleanCube.sign (x i)) / 8

def coefficient (p : Cube → ℝ) (i : Fin 4) : ℝ :=
  moment p false (SS.stdBasis i)

theorem sum_points (f : Cube → ℝ) : ∑ x, f x = ∑ k, f (point k) :=
  (Equiv.sum_comp pointEquiv f).symm

theorem character_single (i : Fin 4) (x : Cube) :
    character (SS.stdBasis i) x = BooleanCube.sign (x i) := by
  have h : ∀ i : Fin 4, ∀ k : Fin 16,
      SS.bdot (SS.stdBasis i) (point k) = point k i := by decide
  obtain ⟨k, rfl⟩ := pointEquiv.surjective x
  change (if SS.bdot (SS.stdBasis i) (point k) then (-1 : ℝ) else 1) = _
  rw [h]
  rfl

theorem probability_nonnegative_iff (a : Fin 4 → ℝ) :
    (∀ x, 0 ≤ probability a x) ↔ ∑ i, |a i| ≤ 1 := by
  have h := BooleanCube.score_nonneg_iff a 1
  simpa [probability, BooleanCube.score, div_nonneg_iff, show ¬(8 : ℝ) ≤ 0 by norm_num] using h

def pairMask (j : Fin 6) : Cube := point (![3, 5, 9, 6, 10, 12] j)

def pairLeft (j : Fin 6) : Fin 4 := ![0, 0, 0, 1, 1, 2] j

def pairRight (j : Fin 6) : Fin 4 := ![1, 2, 3, 2, 3, 3] j

theorem character_pair (j : Fin 6) (x : Cube) :
    character (pairMask j) x =
      BooleanCube.sign (x (pairLeft j)) * BooleanCube.sign (x (pairRight j)) := by
  have h : ∀ j : Fin 6, ∀ x : Cube,
      SS.bdot (pairMask j) x = xor (x (pairLeft j)) (x (pairRight j)) := by decide
  unfold character
  rw [h]
  cases x (pairLeft j) <;> cases x (pairRight j) <;> norm_num [BooleanCube.sign]

def difference (p : Cube → ℝ) (z : Cube) : ℝ :=
  moment p false z - moment p true z

theorem moment_points (p : Cube → ℝ) (b : Bool) (z : Cube) :
    moment p b z = ∑ k, if parity (point k) = b then p (point k) * character z (point k) else 0 :=
  sum_points _

theorem mass_points (p : Cube → ℝ) (b : Bool) :
    mass p b = ∑ k, if parity (point k) = b then p (point k) else 0 :=
  sum_points _

def momentVector (p : Cube → ℝ) : Fin 16 → ℝ :=
  ![mass p false, mass p true,
    difference p (SS.stdBasis 0), difference p (SS.stdBasis 1),
    difference p (SS.stdBasis 2), difference p (SS.stdBasis 3),
    difference p (pairMask 0), difference p (pairMask 1), difference p (pairMask 2),
    difference p (pairMask 3), difference p (pairMask 4), difference p (pairMask 5),
    coefficient p 0, coefficient p 1, coefficient p 2, coefficient p 3]

def normalVector (a : Fin 4 → ℝ) : Fin 16 → ℝ :=
  ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, a 0, a 1, a 2, a 3]

private def charZ (z x : Cube) : ℤ := if SS.bdot z x then -1 else 1

private def columnZ (k : Fin 16) : Fin 16 → ℤ :=
  let e : ℤ := if parity (point k) = false then 1 else 0
  let o : ℤ := if parity (point k) = true then 1 else 0
  let s : ℤ := if parity (point k) then -1 else 1
  ![e, o,
    s * charZ (SS.stdBasis 0) (point k), s * charZ (SS.stdBasis 1) (point k),
    s * charZ (SS.stdBasis 2) (point k), s * charZ (SS.stdBasis 3) (point k),
    s * charZ (pairMask 0) (point k), s * charZ (pairMask 1) (point k),
    s * charZ (pairMask 2) (point k), s * charZ (pairMask 3) (point k),
    s * charZ (pairMask 4) (point k), s * charZ (pairMask 5) (point k),
    e * charZ (SS.stdBasis 0) (point k), e * charZ (SS.stdBasis 1) (point k),
    e * charZ (SS.stdBasis 2) (point k), e * charZ (SS.stdBasis 3) (point k)]

private def column (k : Fin 16) : Fin 16 → ℝ :=
  let e : ℝ := if parity (point k) = false then 1 else 0
  let o : ℝ := if parity (point k) = true then 1 else 0
  let s : ℝ := if parity (point k) then -1 else 1
  ![e, o,
    s * character (SS.stdBasis 0) (point k), s * character (SS.stdBasis 1) (point k),
    s * character (SS.stdBasis 2) (point k), s * character (SS.stdBasis 3) (point k),
    s * character (pairMask 0) (point k), s * character (pairMask 1) (point k),
    s * character (pairMask 2) (point k), s * character (pairMask 3) (point k),
    s * character (pairMask 4) (point k), s * character (pairMask 5) (point k),
    e * character (SS.stdBasis 0) (point k), e * character (SS.stdBasis 1) (point k),
    e * character (SS.stdBasis 2) (point k), e * character (SS.stdBasis 3) (point k)]

private theorem matrix_column (r k : Fin 16) : ParityFourMatrix.matrix r k = column k r := by
  have h : ∀ r k : Fin 16, ParityFourMatrix.matrixZ r k = columnZ k r := by decide
  change (ParityFourMatrix.matrixZ r k : ℝ) = _
  rw [h]
  have hc (z x : Cube) : (charZ z x : ℝ) = character z x := by
    cases h : SS.bdot z x <;> simp [charZ, character, h]
  fin_cases r <;> cases hb : parity (point k) <;> norm_num [columnZ, column, hb, hc]

theorem matrix_mulVec_points (p : Cube → ℝ) :
    ParityFourMatrix.matrix.mulVec (fun k => p (point k)) = momentVector p := by
  funext r
  simp only [Matrix.mulVec, dotProduct, matrix_column]
  fin_cases r <;> norm_num [momentVector] <;>
    simp only [coefficient, difference, moment_points, mass_points] <;>
    try rw [← Finset.sum_sub_distrib]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    cases hb : parity (point k) <;> norm_num [column, hb] <;> ring


set_option maxRecDepth 4000 in
theorem inverse_normalVector (a : Fin 4 → ℝ) (k : Fin 16) :
    ParityFourMatrix.inverse.mulVec (normalVector a) k =
      2 * (1 + ∑ i, a i * BooleanCube.sign (point k i)) := by
  fin_cases k <;>
    norm_num [normalVector, ParityFourMatrix.inverse, ParityFourMatrix.inverseZ,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.succ, point_apply, BooleanCube.sign,
      Nat.testBit, Nat.shiftRight_eq_div_pow] <;> ring_nf <;> rfl

theorem momentEquations_probability (p : Cube → ℝ) (h : MomentEquations p) :
    p = probability (coefficient p) := by
  have hs : ∀ i : Fin 4, SS.hammingWt (SS.stdBasis i) ≤ 2 := by decide
  have hp : ∀ j : Fin 6, SS.hammingWt (pairMask j) ≤ 2 := by decide
  have hd : ∀ z, SS.hammingWt z ≤ 2 → difference p z = 0 := by
    intro z hz
    exact sub_eq_zero.mpr (h.2.2 z hz)
  have hm : ParityFourMatrix.matrix.mulVec (fun k => p (point k)) =
      normalVector (coefficient p) := by
    rw [matrix_mulVec_points]
    simp only [momentVector, normalVector, h.1, h.2.1, hd _ (hs _), hd _ (hp _)]
  have hi := ParityFourMatrix.inverse_reconstruct _ _ hm
  funext x
  obtain ⟨k, rfl⟩ := pointEquiv.surjective x
  have hk := congrFun hi k
  rw [inverse_normalVector] at hk
  simp only [Pi.smul_apply, smul_eq_mul] at hk
  simp only [pointEquiv_apply, probability]
  linarith


theorem probability_momentVector (a : Fin 4 → ℝ) :
    momentVector (probability a) = normalVector a := by
  rw [← matrix_mulVec_points]
  apply ParityFourMatrix.forward_reconstruct
  funext k
  rw [inverse_normalVector]
  simp only [Pi.smul_apply, smul_eq_mul, probability]
  ring

theorem probability_mass (a : Fin 4 → ℝ) (b : Bool) : mass (probability a) b = 1 := by
  have h := probability_momentVector a
  cases b
  · exact congrFun h 0
  · exact congrFun h 1

theorem coefficient_probability (a : Fin 4 → ℝ) : coefficient (probability a) = a := by
  funext i
  have h := probability_momentVector a
  fin_cases i
  · exact congrFun h 12
  · exact congrFun h 13
  · exact congrFun h 14
  · exact congrFun h 15

theorem probability_momentEquations (a : Fin 4 → ℝ) : MomentEquations (probability a) := by
  refine ⟨probability_mass _ _, probability_mass _ _, ?_⟩
  intro z hz
  have hm : z = point 0 ∨ (∃ i, z = SS.stdBasis i) ∨ ∃ j, z = pairMask j := by
    have h : ∀ z : Cube, SS.hammingWt z ≤ 2 →
        z = point 0 ∨ (∃ i, z = SS.stdBasis i) ∨ ∃ j, z = pairMask j := by decide
    exact h z hz
  have hzero : ∀ x : Cube, character (point 0) x = 1 := by
    intro x
    have hb : SS.bdot (point 0) x = false := by
      have : ∀ x : Cube, SS.bdot (point 0) x = false := by decide
      exact this x
    simp [character, hb]
  have hs : ∀ i : Fin 4, difference (probability a) (SS.stdBasis i) = 0 := by
    intro i
    have h := probability_momentVector a
    fin_cases i
    · exact congrFun h 2
    · exact congrFun h 3
    · exact congrFun h 4
    · exact congrFun h 5
  have hp : ∀ j : Fin 6, difference (probability a) (pairMask j) = 0 := by
    intro j
    have h := probability_momentVector a
    fin_cases j
    · exact congrFun h 6
    · exact congrFun h 7
    · exact congrFun h 8
    · exact congrFun h 9
    · exact congrFun h 10
    · exact congrFun h 11
  rcases hm with rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
  · have hf : ∀ b, moment (probability a) b (point 0) = mass (probability a) b := by
      intro b
      simp only [moment, hzero, mul_one, mass]
    rw [hf, hf, probability_mass, probability_mass]
  · exact sub_eq_zero.mp (hs i)
  · exact sub_eq_zero.mp (hp j)


theorem feasible_iff_crosspolytope (p : Cube → ℝ) :
    ((∀ x, 0 ≤ p x) ∧ MomentEquations p) ↔
      ∃ a : Fin 4 → ℝ, (∑ i, |a i| ≤ 1) ∧ p = probability a := by
  constructor
  · rintro ⟨hn, he⟩
    have hp := momentEquations_probability p he
    refine ⟨coefficient p, ?_, hp⟩
    apply (probability_nonnegative_iff _).1
    rwa [← hp]
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(probability_nonnegative_iff _).2 ha, probability_momentEquations a⟩

theorem probability_injective : Function.Injective probability := by
  intro a b h
  have hc := congrArg coefficient h
  simpa only [coefficient_probability] using hc

end
end MainTheory.ParityFour
