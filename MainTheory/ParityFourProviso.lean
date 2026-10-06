import MainTheory.ParityFourEdgeIsolation
import SixQubit.Common

/-!
# The representation proviso of `lem:parity4-edgeisolation`

`MainTheory.ParityFourEdgeIsolation` proves the character inversion the
manuscript's edge-isolation lemma runs on, but takes the character equations
as hypotheses.  Its header records what was missing: the manuscript's proviso
that "the four effective parity coordinates are represented by physical
single-qubit `Z` characters and the flipped coordinate is a physical
single-qubit flip".

This file supplies it, by construction rather than by assumption.  The four
effective coordinates are named by an injection `emb : Fin 4 -> Fin 6`; the
physical Pauli carrying an effective mask `z` is the pushforward
`push emb z`, and the physical flip of coordinate `k` is
`push emb (single k)`.  Then

* `bdot_push` -- the physical `Z`-dressing computes the effective character:
  `bdot (push emb z) y = bdot z (proj emb y)`;
* `proj_bxor_push` -- the physical flip induces the effective flip;
* `row_eq_character_sum` -- the Knill--Laflamme row for the physical error
  with `X`-part `push emb (single k)` and `Z`-part `push emb z` is exactly the
  effective character sum, times the row phase `chi_z(e_k)`.  That factor is
  the manuscript's "up to row phases", and it is a sign, so it does not
  affect vanishing;
* `edgeMasks_eq` -- the eight dressings the manuscript writes down, `1`,
  `chi_k`, `chi_j` and `chi_k chi_j` for `j != k`, are exactly the masks whose
  weight off coordinate `k` is at most one.  As physical errors these are
  `X_k`, `Y_k`, `Z_jX_k` and `Z_jY_k`, the manuscript's
  `eq:parity4-edgeerrors`;
* `edgeMasks_transversal` -- those eight meet every class modulo the all-ones
  vector, which is the content of "the complete character table of a
  three-dimensional Boolean group";
* `edge_isolation` -- `lem:parity4-edgeisolation` itself.

The remaining hypotheses are the manuscript's own inputs: that the
off-diagonal Knill--Laflamme equations hold for those eight physical errors,
and that flipping coordinate `k` carries the incidence set into the even
parity class.  Nothing about the representation is assumed any more.
-/

namespace MainTheory.ParityFour

open scoped BigOperators

noncomputable section

/-- The physical `Z`-dressing carrying an effective mask: it is supported on
the four effective qubits and agrees with `z` there. -/
def push (emb : Fin 4 → Fin 6) (z : Cube) : SS.BitString 6 :=
  fun i => decide (∃ j, emb j = i ∧ z j = true)

/-- The effective mask carried by a physical string. -/
def proj (emb : Fin 4 → Fin 6) (y : SS.BitString 6) : Cube := fun j => y (emb j)

/-- The mask of a single effective coordinate. -/
def single (k : Fin 4) : Cube := fun j => decide (j = k)

@[simp] theorem proj_apply (emb : Fin 4 → Fin 6) (y : SS.BitString 6) (j : Fin 4) :
    proj emb y j = y (emb j) := rfl

theorem push_emb {emb : Fin 4 → Fin 6} (hemb : Function.Injective emb)
    (z : Cube) (j : Fin 4) : push emb z (emb j) = z j := by
  cases hzj : z j
  · simp only [push, decide_eq_false_iff_not, not_exists, not_and]
    intro i hi hzi
    rw [hemb hi, hzj] at hzi
    exact Bool.noConfusion hzi
  · simp only [push, decide_eq_true_eq]
    exact ⟨j, rfl, hzj⟩

/-- **The dressing is the character.**  A physical `Z`-mask pushed forward
along the four effective coordinates computes the effective character. -/
theorem bdot_push {emb : Fin 4 → Fin 6} (hemb : Function.Injective emb)
    (z : Cube) (y : SS.BitString 6) :
    SS.bdot (push emb z) y = SS.bdot z (proj emb y) := by
  have himg : (Finset.univ.filter fun i : Fin 6 => push emb z i && y i)
      = (Finset.univ.filter fun j : Fin 4 => z j && y (emb j)).image emb := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      push, decide_eq_true_eq, Bool.and_eq_true]
    constructor
    · rintro ⟨⟨j, hj, hz⟩, hy⟩
      exact ⟨j, ⟨hz, hj ▸ hy⟩, hj⟩
    · rintro ⟨j, ⟨hz, hy⟩, rfl⟩
      exact ⟨⟨j, rfl, hz⟩, hy⟩
  simp only [SS.bdot, proj]
  rw [himg, Finset.card_image_of_injective _ hemb]

/-- **The flip is the flip.**  The physical single-qubit flip at the qubit
carrying effective coordinate `k` induces the flip of that coordinate. -/
theorem proj_bxor_push {emb : Fin 4 → Fin 6} (hemb : Function.Injective emb)
    (y : SS.BitString 6) (k : Fin 4) :
    proj emb (SS.bxor y (push emb (single k))) = SS.bxor (proj emb y) (single k) := by
  funext j
  simp only [proj, SS.bxor, push_emb hemb]

/-- The incidence overlap carried by an even effective string: the sum, over
the fibre of physical strings above it, of `c^dagger d` on the incidence. -/
def overlap (emb : Fin 4 → Fin 6) (c d : SS.BitString 6 → ℂ)
    (I : Finset (SS.BitString 6)) (e : SS.BitString 6) (x : Cube) : ℂ :=
  ∑ y ∈ I with proj emb (SS.bxor y e) = x, star (c (SS.bxor y e)) * d y

theorem signMul_bdot (z x : Cube) (v : ℂ) :
    SixQubit.signMul (SS.bdot z x) v = ((character z x : ℝ) : ℂ) * v := by
  by_cases h : SS.bdot z x <;> simp [SixQubit.signMul, character, h]

/-- **The Knill--Laflamme row is the character sum.**

The physical error with `X`-part the flip of coordinate `k` and `Z`-part the
pushforward of `z` contributes, on the incidence set, exactly the effective
character sum of the overlaps, times the sign `chi_z(e_k)`.  That sign is the
manuscript's "up to row phases". -/
theorem row_eq_character_sum {emb : Fin 4 → Fin 6} (hemb : Function.Injective emb)
    (c d : SS.BitString 6 → ℂ) (I : Finset (SS.BitString 6)) (k : Fin 4) (z : Cube) :
    (∑ y ∈ I, SixQubit.signMul (SS.bdot (push emb z) y)
        (star (c (SS.bxor y (push emb (single k)))) * d y))
      = ((character z (single k) : ℝ) : ℂ)
          * ∑ x : Cube, ((character z x : ℝ) : ℂ)
              * overlap emb c d I (push emb (single k)) x := by
  rw [Finset.mul_sum, ← Finset.sum_fiberwise I
    (fun y => proj emb (SS.bxor y (push emb (single k))))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [overlap, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hx : proj emb (SS.bxor y (push emb (single k))) = x := (Finset.mem_filter.1 hy).2
  have hpy : proj emb y = SS.bxor x (single k) := by
    rw [← hx, proj_bxor_push hemb, SS.bxor_assoc, SS.bxor_self, SS.bxor_zero]
  rw [bdot_push hemb, hpy, signMul_bdot, character_bxor]
  push_cast
  ring

/-! ## The eight dressings -/

/-- The manuscript's `eq:parity4-edgeerrors`, as effective masks: `1`,
`chi_k`, `chi_j` and `chi_k chi_j` for `j != k` are exactly the masks of
weight at most one away from `k`. -/
theorem edgeMasks_eq (k : Fin 4) (z : Cube) :
    SS.hammingWt (Function.update z k false) ≤ 1 ↔
      z = (fun _ => false) ∨ z = single k ∨
        ∃ j, j ≠ k ∧ (z = single j ∨ z = SS.bxor (single k) (single j)) := by
  revert k z
  decide

/-- **The complete character table.**  The eight dressings meet every class
of the cube modulo the all-ones vector. -/
theorem edgeMasks_transversal (k : Fin 4) (z : Cube) :
    SS.hammingWt (Function.update z k false) ≤ 1 ∨
      SS.hammingWt (Function.update (SS.bxor z allOnes) k false) ≤ 1 := by
  revert k z
  decide

/-! ## The lemma -/

/-- **`lem:parity4-edgeisolation`.**

Let `emb` name the four effective parity coordinates among the six physical
qubits, `k` be the flipped coordinate, and `I` the incidence set.  If the
off-diagonal Knill--Laflamme equation holds for each of the eight physical
errors of `eq:parity4-edgeerrors` -- `X_k`, `Y_k`, `Z_jX_k` and `Z_jY_k`,
which are the dressings of weight at most one away from `k` -- and flipping
`k` carries the incidence set into the even parity class, then every
incidence overlap vanishes.  For a two-dimensional spinor the overlap at `x`
is `c_x^dagger d_{x+e_k}`, which is `eq:parity4-edgeorthogonality`.

The representation proviso is discharged, not assumed: the physical errors
here are literally the pushforwards of the effective masks. -/
theorem edge_isolation {emb : Fin 4 → Fin 6} (hemb : Function.Injective emb)
    (k : Fin 4) (c d : SS.BitString 6 → ℂ) (I : Finset (SS.BitString 6))
    (hpar : ∀ y ∈ I, parity (proj emb (SS.bxor y (push emb (single k)))) = false)
    (hKL : ∀ z : Cube, SS.hammingWt (Function.update z k false) ≤ 1 →
      (∑ y ∈ I, SixQubit.signMul (SS.bdot (push emb z) y)
        (star (c (SS.bxor y (push emb (single k)))) * d y)) = 0) :
    overlap emb c d I (push emb (single k)) = 0 := by
  refine eq_zero_of_transversal ?_
    {z : Cube | SS.hammingWt (Function.update z k false) ≤ 1}
    (fun z => edgeMasks_transversal k z) ?_
  · intro x hx
    simp only [overlap]
    refine Finset.sum_eq_zero fun y hy => ?_
    obtain ⟨hyI, hyx⟩ := Finset.mem_filter.1 hy
    have hfalse : parity x = false := hyx ▸ hpar y hyI
    rw [hx] at hfalse
    exact absurd hfalse (by simp)
  · intro z hz
    have hrow := hKL z hz
    rw [row_eq_character_sum hemb c d I k z] at hrow
    have hchar : ((character z (single k) : ℝ) : ℂ) ≠ 0 := by
      have : (character z (single k) : ℝ) ≠ 0 := by
        unfold character
        split <;> norm_num
      simpa using this
    exact (mul_eq_zero.1 hrow).resolve_left hchar

end

end MainTheory.ParityFour
