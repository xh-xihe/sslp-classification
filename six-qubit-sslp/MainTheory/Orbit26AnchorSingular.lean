import SixQubit.Block26

/-!
# `lem:q4o26anchorsingular`

The manuscript's orbit-26 argument, after `lem:q4o26Jorth`, shows that the two
anchor blocks are singular.  Writing `C_g`, `D_g` for the bottom and top
`2 x 2` blocks of group `g`, with `g = 3` the anchor, the equations in play are

  `eq:q4o26anchormatrix`   `C_3^dagger D_g + (C_g^dagger D_3)^T = 0`,  `g <= 2`;
  `eq:q4o26outermatrix`    `conj(C_g) J D_h^T + conj(C_h) J D_g^T = 0`, `g < h <= 2`;
  `eq:q4o26matrixmoment`   `C_g C_g^dagger + D_g D_g^dagger = rho/2`.

If `C_3` is invertible the first gives `D_g = -M conj(C_g)` with
`M = (C_3^dagger)^{-1} D_3^T`, and substituting into the second gives
`F_gh M^T = 0` for `F_gh = conj(C_g) J conj(C_h)^T + conj(C_h) J conj(C_g)^T`.

This file proves the two pieces that argument needs and are not already in
`SixQubit.Block26`:

* a genericity step -- a single row vector can be chosen off finitely many
  lines at once, which is what "choose `w` outside the finitely many kernels"
  means over an infinite field;
* the algebraic core -- three nonzero `2 x 2` blocks whose `F_gh` all vanish,
  one of them with both columns nonzero, are impossible.

Both places where `SixQubit.Block26.axis_lemma` -- the manuscript's
`lem:q4o26Jorth` -- is consumed are covered: `core` is the branch where `D_3`
is invertible and a generic row is chosen, and `core_rank_one` is the branch
where `D_3` has rank one and the row is the unit vector spanning its columns.

## What this file does NOT prove

`lem:q4o26anchorsingular` itself is not proved here, and stays on the
not-formalized list.  Three things are missing between these cores and the
lemma:

* the `2 x 2` matrix reduction -- solving `eq:q4o26anchormatrix` for
  `D_g = -M conj(C_g)` with `M = (C_3^dagger)^{-1} D_3^T` when `C_3` is
  invertible, substituting into `eq:q4o26outermatrix` to get `F_gh M^T = 0`,
  and cancelling `M^T`;
* the norm bookkeeping of `eq:q4o26rnormlarge`, which turns
  `eq:q4o26matrixmoment` for the anchor group into the strict bound
  `sum_g ||r_g||^2 > 1/2` feeding `core_rank_one`, together with the per-group
  bound `1/4` and the per-axis bound `3/8` from the hexagon inequalities;
* the closing sentence "the equations are symmetric under interchanging the two
  logical states", which is how the manuscript gets `D_3` singular from the
  argument that gives `C_3` singular.

What is here is the mathematics those steps feed into, stated so that supplying
them is bookkeeping rather than a new idea.
-/

namespace MainTheory.Orbit26

open scoped BigOperators
open SixQubit.Block26

/-! ## Choosing a generic row -/

/-- For a nonzero `c : ℂ × ℂ`, the scalars `t` with `c.1 + t * c.2 = 0` form a
subsingleton: at most one `t` is bad. -/
theorem bad_subsingleton {c1 c2 : ℂ} (hc : ¬(c1 = 0 ∧ c2 = 0)) {s t : ℂ}
    (hs : c1 + s * c2 = 0) (ht : c1 + t * c2 = 0) : s = t := by
  by_cases h2 : c2 = 0
  · exact absurd ⟨by simpa [h2] using hs, h2⟩ hc
  · have : (s - t) * c2 = 0 := by linear_combination hs - ht
    rcases mul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h h2

/-- **The genericity step.**

Given finitely many nonzero vectors of `ℂ^2`, presented as a list of pairs,
there is a single `t` with `c.1 + t * c.2 ≠ 0` for every one of them.  This is
"choose `w` outside the finitely many kernels": the row is `w = (1, t)`, each
kernel excludes at most one `t`, and `ℂ` is infinite. -/
theorem exists_generic (L : List (ℂ × ℂ)) (hL : ∀ c ∈ L, ¬(c.1 = 0 ∧ c.2 = 0)) :
    ∃ t : ℂ, ∀ c ∈ L, c.1 + t * c.2 ≠ 0 := by
  classical
  -- the bad values, one per entry with a nonzero second coordinate
  let bad : Finset ℂ :=
    (L.filter fun c => c.2 ≠ 0).toFinset.image fun c => -c.1 / c.2
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
  refine ⟨t, fun c hc hzero => ht ?_⟩
  have hc2 : c.2 ≠ 0 := by
    intro h2
    exact hL c hc ⟨by simpa [h2] using hzero, h2⟩
  have hmem : c ∈ (L.filter fun c => c.2 ≠ 0).toFinset := by
    simp [List.mem_toFinset, hc, hc2]
  have hval : t = -c.1 / c.2 := by
    field_simp at hzero ⊢
    linear_combination hzero
  rw [hval]
  exact Finset.mem_image.2 ⟨c, hmem, rfl⟩


/-! ## The algebraic core

Three `2 x 2` blocks `A_0, A_1, A_2` -- in the manuscript these are the
conjugated non-anchor blocks `conj(C_g)` -- with all their `F_gh` vanishing.
`F_gh = 0` is used only through its quadratic form: for a row `w`,

  `w^T F_gh w = 2 * Jform (w^T A_g) (w^T A_h)`,

so the hypothesis is stated as the vanishing of that `Jform` for every `w`,
which for the symmetric `F` is equivalent to `F_gh = 0` itself and is what the
manuscript uses.  Rows are taken as `w = (1, t)`, which loses nothing: the
manuscript's `w` is chosen generically and any `w` with a zero first entry is a
limit of such. -/

/-- A nonzero `2 x 2` block has a nonzero column. -/
theorem exists_nonzero_col {a b c d : ℂ}
    (h : ¬(a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    ¬(a = 0 ∧ c = 0) ∨ ¬(b = 0 ∧ d = 0) := by tauto

/-- The closing step: three pairwise `J`-orthogonal rows, one of which has both
entries nonzero, contradict `lem:q4o26Jorth`. -/
theorem finish_of_rows {r0a r0b r1a r1b r2a r2b : ℂ}
    (h0a : r0a ≠ 0) (h0b : r0b ≠ 0)
    (h1 : ¬(r1a = 0 ∧ r1b = 0)) (h2 : ¬(r2a = 0 ∧ r2b = 0))
    (e01 : Jform r0a r0b r1a r1b = 0)
    (e02 : Jform r0a r0b r2a r2b = 0)
    (e12 : Jform r1a r1b r2a r2b = 0) : False := by
  rcases axis_lemma r0a r0b r1a r1b r2a r2b (fun h => h0a h.1) h1 h2 e01 e02 e12 with
    ⟨hb0, _, _⟩ | ⟨ha0, _, _⟩
  · exact h0b hb0
  · exact h0a ha0

/-- **The core of `lem:q4o26anchorsingular`.**

`A_0` has both columns nonzero, `A_1` and `A_2` are nonzero, and every pair is
`J`-orthogonal after any row `(1, t)` is applied.  This is impossible. -/
theorem core
    {a0 b0 c0 d0 a1 b1 c1 d1 a2 b2 c2 d2 : ℂ}
    (hcol0 : ¬(a0 = 0 ∧ c0 = 0)) (hcol1 : ¬(b0 = 0 ∧ d0 = 0))
    (hA1 : ¬(a1 = 0 ∧ b1 = 0 ∧ c1 = 0 ∧ d1 = 0))
    (hA2 : ¬(a2 = 0 ∧ b2 = 0 ∧ c2 = 0 ∧ d2 = 0))
    (e01 : ∀ t : ℂ, Jform (a0 + t * c0) (b0 + t * d0) (a1 + t * c1) (b1 + t * d1) = 0)
    (e02 : ∀ t : ℂ, Jform (a0 + t * c0) (b0 + t * d0) (a2 + t * c2) (b2 + t * d2) = 0)
    (e12 : ∀ t : ℂ, Jform (a1 + t * c1) (b1 + t * d1) (a2 + t * c2) (b2 + t * d2) = 0) :
    False := by
  classical
  rcases exists_nonzero_col hA1 with h1 | h1 <;>
    rcases exists_nonzero_col hA2 with h2 | h2
  · obtain ⟨t, ht⟩ := exists_generic [(a0, c0), (b0, d0), (a1, c1), (a2, c2)]
      (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> dsimp only <;>
          first | exact hcol0 | exact hcol1 | exact h1 | exact h2)
    exact finish_of_rows (ht (a0, c0) (by simp)) (ht (b0, d0) (by simp))
      (fun h => ht (a1, c1) (by simp) h.1) (fun h => ht (a2, c2) (by simp) h.1)
      (e01 t) (e02 t) (e12 t)
  · obtain ⟨t, ht⟩ := exists_generic [(a0, c0), (b0, d0), (a1, c1), (b2, d2)]
      (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> dsimp only <;>
          first | exact hcol0 | exact hcol1 | exact h1 | exact h2)
    exact finish_of_rows (ht (a0, c0) (by simp)) (ht (b0, d0) (by simp))
      (fun h => ht (a1, c1) (by simp) h.1) (fun h => ht (b2, d2) (by simp) h.2)
      (e01 t) (e02 t) (e12 t)
  · obtain ⟨t, ht⟩ := exists_generic [(a0, c0), (b0, d0), (b1, d1), (a2, c2)]
      (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> dsimp only <;>
          first | exact hcol0 | exact hcol1 | exact h1 | exact h2)
    exact finish_of_rows (ht (a0, c0) (by simp)) (ht (b0, d0) (by simp))
      (fun h => ht (b1, d1) (by simp) h.2) (fun h => ht (a2, c2) (by simp) h.1)
      (e01 t) (e02 t) (e12 t)
  · obtain ⟨t, ht⟩ := exists_generic [(a0, c0), (b0, d0), (b1, d1), (b2, d2)]
      (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> dsimp only <;>
          first | exact hcol0 | exact hcol1 | exact h1 | exact h2)
    exact finish_of_rows (ht (a0, c0) (by simp)) (ht (b0, d0) (by simp))
      (fun h => ht (b1, d1) (by simp) h.2) (fun h => ht (b2, d2) (by simp) h.2)
      (e01 t) (e02 t) (e12 t)


/-! ## The rank-one branch

When `C_3` is invertible but `D_3` has rank one, the manuscript does not choose
a generic row.  It takes the unit vector `d` spanning the columns of `D_3`,
notes that `M^T` has image spanned by `d` so that `eq:q4o26FM` gives
`F_gh d = 0`, and sets `r_g := d^T conj(C_g)`.  The three rows are then
pairwise `J`-orthogonal, and their total squared norm exceeds `1/2` by
`eq:q4o26rnormlarge` while each single group contributes at most `1/4` and each
coordinate axis carries at most `3/8`.

That is the second application of `lem:q4o26Jorth`, and it is what
`core_rank_one` below packages. -/

/-- **The rank-one core of `lem:q4o26anchorsingular`.**

Three pairwise `J`-orthogonal rows whose total squared norm exceeds `1/2`,
with each row contributing at most `1/4` and each coordinate axis at most
`3/8`, are impossible. -/
theorem core_rank_one {r0a r0b r1a r1b r2a r2b : ℂ}
    (e01 : Jform r0a r0b r1a r1b = 0)
    (e02 : Jform r0a r0b r2a r2b = 0)
    (e12 : Jform r1a r1b r2a r2b = 0)
    (q0 : Complex.normSq r0a + Complex.normSq r0b ≤ 1 / 4)
    (q1 : Complex.normSq r1a + Complex.normSq r1b ≤ 1 / 4)
    (q2 : Complex.normSq r2a + Complex.normSq r2b ≤ 1 / 4)
    (hbig : 1 / 2 < Complex.normSq r0a + Complex.normSq r0b
      + (Complex.normSq r1a + Complex.normSq r1b)
      + (Complex.normSq r2a + Complex.normSq r2b))
    (hax1 : Complex.normSq r0a + Complex.normSq r1a + Complex.normSq r2a ≤ 3 / 8)
    (hax2 : Complex.normSq r0b + Complex.normSq r1b + Complex.normSq r2b ≤ 3 / 8) :
    False := by
  -- every row is nonzero: a vanishing one leaves at most `1/4 + 1/4`
  have h0 : ¬(r0a = 0 ∧ r0b = 0) := by
    rintro ⟨hx, hy⟩
    rw [hx, hy] at hbig
    simp only [map_zero] at hbig
    linarith
  have h1 : ¬(r1a = 0 ∧ r1b = 0) := by
    rintro ⟨hx, hy⟩
    rw [hx, hy] at hbig
    simp only [map_zero] at hbig
    linarith
  have h2 : ¬(r2a = 0 ∧ r2b = 0) := by
    rintro ⟨hx, hy⟩
    rw [hx, hy] at hbig
    simp only [map_zero] at hbig
    linarith
  rcases axis_lemma r0a r0b r1a r1b r2a r2b h0 h1 h2 e01 e02 e12 with
    ⟨hb0, hb1, hb2⟩ | ⟨ha0, ha1, ha2⟩
  · rw [hb0, hb1, hb2] at hbig
    simp only [map_zero] at hbig
    linarith
  · rw [ha0, ha1, ha2] at hbig
    simp only [map_zero] at hbig
    linarith

end MainTheory.Orbit26
