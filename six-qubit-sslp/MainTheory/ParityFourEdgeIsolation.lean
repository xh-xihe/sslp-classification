import MainTheory.ParityFourMoments
import SS.BridgeD3

/-!
# The character inversion behind `lem:parity4-edgeisolation`

The manuscript's edge-isolation lemma says that the off-diagonal
Knill--Laflamme rows for the weight-at-most-two errors `X_k`, `Y_k`, `Z_jX_k`
and `Z_jY_k` are, up to row phases, the characters `1`, `chi_k`, `chi_j` and
`chi_k chi_j`; that these are the complete character table of a Boolean group,
so the coefficient matrix `W_k` satisfies `W_k W_k^T = 8 I`; and that every
incidence overlap therefore vanishes.

This file proves the mathematical core of that argument -- the inversion --
in the form it is actually used, and it proves it on the whole
four-coordinate cube rather than on one incidence set, which is where it is
reusable.

What is *not* proved here is the manuscript's proviso: that the four effective
parity coordinates really are represented by physical single-qubit `Z`
characters, and the flipped coordinate by a physical single-qubit flip.  That
proviso is what turns the Knill--Laflamme rows into the characters below, and
it is assumed, not derived.  `edge_isolation_of_character_rows` therefore
takes the character equations as hypotheses, and `lem:parity4-edgeisolation`
stays on the not-formalized list rather than being cited from here.

NOT-FORMALIZED: lem:parity4-edgeisolation
-/

namespace MainTheory.ParityFour

open scoped BigOperators

set_option maxRecDepth 8000

/-- A character is multiplicative in its second argument along `bxor`. -/
theorem character_bxor (z x y : Cube) :
    character z (SS.bxor x y) = character z x * character z y := by
  simp only [character, SS.bdot_bxor_right]
  by_cases hx : SS.bdot z x <;> by_cases hy : SS.bdot z y <;>
    simp [hx, hy]

/-- `bxor` vanishes exactly on the diagonal. -/
theorem bxor_eq_false_iff (x y : Cube) :
    SS.bxor x y = (fun _ => false) ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [SS.bxor] at hi
    revert hi
    cases hx : x i <;> cases hy : y i <;> simp
  · rintro rfl
    exact SS.bxor_self x

/-- **The character sum.**  Summing one character over the whole cube gives
`16` at the trivial argument and `0` elsewhere. -/
theorem sum_character (w : Cube) :
    ∑ z : Cube, character z w = if w = (fun _ => false) then 16 else 0 := by
  obtain ⟨j, rfl⟩ := pointEquiv.surjective w
  rw [sum_points]
  fin_cases j <;>
    simp (config := { decide := true }) only [character, Fin.sum_univ_succ,
      Fin.sum_univ_zero, if_true, if_false] <;>
    norm_num

/-- **Orthogonality of the sixteen characters.** -/
theorem sum_character_mul (x y : Cube) :
    ∑ z : Cube, character z x * character z y = if x = y then 16 else 0 := by
  have h : ∀ z : Cube, character z x * character z y = character z (SS.bxor x y) :=
    fun z => (character_bxor z x y).symm
  rw [Finset.sum_congr rfl fun z _ => h z, sum_character]
  by_cases hxy : x = y
  · subst hxy
    simp [SS.bxor_self]
  · have hne : SS.bxor x y ≠ (fun _ => false) := fun h => hxy ((bxor_eq_false_iff x y).1 h)
    simp [hne, hxy]

/-- **Fourier inversion on the parity cube.**

A complex function whose every character sum vanishes is zero.  This is the
manuscript's `W_k W_k^T = 8 I` step, stated as the inversion it is used for
and on the full cube. -/
theorem eq_zero_of_character_sums {u : Cube → ℂ}
    (h : ∀ z : Cube, ∑ x : Cube, (character z x : ℂ) * u x = 0) (x : Cube) :
    u x = 0 := by
  have key : ∑ z : Cube, (character z x : ℂ) * (∑ y : Cube, (character z y : ℂ) * u y)
      = 16 * u x := by
    have expand : ∀ z : Cube,
        (character z x : ℂ) * (∑ y : Cube, (character z y : ℂ) * u y)
          = ∑ y : Cube, ((character z x * character z y : ℝ) : ℂ) * u y := by
      intro z
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by push_cast; ring
    rw [Finset.sum_congr rfl fun z _ => expand z, Finset.sum_comm]
    have inner : ∀ y : Cube,
        ∑ z : Cube, ((character z x * character z y : ℝ) : ℂ) * u y
          = (if x = y then (16 : ℂ) else 0) * u y := by
      intro y
      rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_character_mul]
      by_cases hxy : x = y <;> simp [hxy]
    rw [Finset.sum_congr rfl fun y _ => inner y]
    simp
  rw [Finset.sum_congr rfl fun z _ => by rw [h z, mul_zero]] at key
  have : (16 : ℂ) * u x = 0 := by
    rw [← key]
    simp
  simpa using this

/-- **`lem:parity4-edgeisolation`, under its own proviso.**

Given eight incidence overlaps `u` on the parity cube whose every character
sum vanishes -- which is what the manuscript's Knill--Laflamme rows become
once its representation proviso is granted -- every overlap vanishes.

The hypothesis is the conclusion of the proviso, not the Knill--Laflamme
equations themselves, so this is the lemma's algebra and not the lemma. -/
theorem edge_isolation_of_character_rows {u : Cube → ℂ}
    (h : ∀ z : Cube, ∑ x : Cube, (character z x : ℂ) * u x = 0) :
    u = 0 :=
  funext fun x => eq_zero_of_character_sums h x


/-! ## Halving the hypothesis: eight rows, not sixteen

The manuscript's argument does not have sixteen character equations.  For a
fixed flipped coordinate it has eight -- `1`, `chi_k`, `chi_j` and
`chi_k chi_j` for `j != k` -- and calls them "the complete character table of a
three-dimensional Boolean group".  That phrase is the following observation:
the incidence overlaps live on the even parity class, the all-ones character
is identically `1` there, so a character sum depends only on the class of `z`
modulo the all-ones vector, and eight suitably chosen rows meet every class.

`eq_zero_of_transversal` is that step.  It is what closes the gap between the
sixteen-row inversion above and the eight rows the manuscript writes down. -/

/-- The all-ones vector; `parity` is its character. -/
def allOnes : Cube := fun _ => true

theorem parity_eq_bdot (x : Cube) : parity x = SS.bdot allOnes x := rfl

theorem bdot_comm (s t : Cube) : SS.bdot s t = SS.bdot t s := by
  simp [SS.bdot, Bool.and_comm]

theorem character_bxor_left (z w x : Cube) :
    character (SS.bxor z w) x = character z x * character w x := by
  simp only [character, bdot_comm (SS.bxor z w) x, bdot_comm z x, bdot_comm w x,
    SS.bdot_bxor_right]
  by_cases hz : SS.bdot x z <;> by_cases hw : SS.bdot x w <;> simp [hz, hw]

/-- On a function supported in the even parity class, the character sum is
unchanged by adding the all-ones vector: `chi_1` is identically `1` there. -/
theorem sum_bxor_allOnes {u : Cube → ℂ}
    (hsupp : ∀ x, parity x = true → u x = 0) (z : Cube) :
    ∑ x, ((character (SS.bxor z allOnes) x : ℝ) : ℂ) * u x
      = ∑ x, ((character z x : ℝ) : ℂ) * u x := by
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : parity x = true
  · rw [hsupp x hx, mul_zero, mul_zero]
  · have hpar : parity x = false := by simpa using hx
    have hone : character allOnes x = 1 := by
      have hb : SS.bdot allOnes x = false := by rw [← parity_eq_bdot]; exact hpar
      simp [character, hb]
    rw [character_bxor_left, hone, mul_one]

/-- **Eight rows suffice.**

If `u` is supported in the even parity class and `T` meets every class of
`Cube` modulo the all-ones vector, then the character sums over `T` alone
force `u = 0`.  A set of eight rows meeting every class is exactly what the
manuscript's `1`, `chi_k`, `chi_j`, `chi_k chi_j` provide. -/
theorem eq_zero_of_transversal {u : Cube → ℂ}
    (hsupp : ∀ x, parity x = true → u x = 0)
    (T : Set Cube) (hT : ∀ z : Cube, z ∈ T ∨ SS.bxor z allOnes ∈ T)
    (h : ∀ z ∈ T, ∑ x, ((character z x : ℝ) : ℂ) * u x = 0) :
    u = 0 := by
  refine edge_isolation_of_character_rows fun z => ?_
  rcases hT z with hz | hz
  · exact h z hz
  · rw [← sum_bxor_allOnes hsupp z]
    exact h _ hz

/-- The rows with a fixed coordinate clear form such a transversal: `z` and
`z + 1` differ in every coordinate, so exactly one of them is clear at `k`. -/
theorem eq_zero_of_clear_coordinate (k : Fin 4) {u : Cube → ℂ}
    (hsupp : ∀ x, parity x = true → u x = 0)
    (h : ∀ z : Cube, z k = false →
      ∑ x, ((character z x : ℝ) : ℂ) * u x = 0) :
    u = 0 := by
  refine eq_zero_of_transversal hsupp {z : Cube | z k = false} ?_ (fun z hz => h z hz)
  intro z
  by_cases hk : z k = false
  · exact Or.inl hk
  · refine Or.inr ?_
    have hz : z k = true := by simpa using hk
    show SS.bxor z allOnes k = false
    simp [SS.bxor, allOnes, hz]

end MainTheory.ParityFour
