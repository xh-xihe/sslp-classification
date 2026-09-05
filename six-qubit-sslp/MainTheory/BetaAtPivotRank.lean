import MainTheory.D3FreshSparseAssembly
import MainTheory.BetaExists

/-!
# `q <= beta_r` at arbitrary length

`eq:d3-full-bound` and `eq:d3-sslp-bound` both read

  `m | q`, `q | d_r(C)`, `q <= beta_r <= beta_n`,

with `r` the size of the pivot -- by `lem:common-affine-span` the common affine
dimension of the two actual logical supports.  What this package proved at
arbitrary `n` was only the weaker `q <= beta_n`:
`D3FreshSparseAssembly.FreshSparsePhase.order_le_of_betaBound` takes a
`BetaBound n B` and uses the pivot's rank only to discharge `rank <= n`.  The
sharper form existed for six qubits alone (`SupportAffineRank`).

Nothing about the bound needs the ambient length.  The sparse pivot's minor is
a nonsingular zero--one matrix of size exactly `F.basis.rank`, so a
`BetaBound` *at that rank* already applies to it, and `BetaExists.betaOf`
supplies one at every size.  `betaOf` is a supremum over all sizes up to its
argument, so it is monotone and `beta_r <= beta_n` is immediate.
-/

namespace MainTheory.BetaAtPivotRank

open MainTheory
open MainTheory.D3FreshSparseAssembly

variable {n : ℕ}

/-- `betaOf` is monotone: it is a supremum over an initial segment. -/
theorem betaOf_mono {r N : ℕ} (h : r ≤ N) :
    MainTheory.BetaExists.betaOf r ≤ MainTheory.BetaExists.betaOf N := by
  refine Finset.sup_mono ?_
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

/-- **A binary denominator bound at the pivot's own rank bounds the order.**

Same proof as `order_le_of_betaBound`, with the bound applied at `rank` rather
than at `n`; the minor's size is `rank` on the nose. -/
theorem FreshSparsePhase.order_le_of_betaBound_rank {B : ℕ}
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta)
    (beta : BinaryBeta.BetaBound F.basis.rank B) :
    F.data.order ≤ B := by
  have hden : SharpClearing.inverseDenominator F.data.minor ≤ B :=
    beta F.basis.rank F.rank_pos le_rfl F.data.minor
      F.minor_isZeroOne F.data.minor_nonsingular
  have hord : F.data.order ≤ SharpClearing.inverseDenominator F.data.minor :=
    Nat.le_of_dvd
      (SharpClearing.inverseDenominator_pos F.data.minor)
      F.order_dvd_inverseDenominator
  exact hord.trans hden

/-- **`q <= beta_r`, unconditionally and at arbitrary length.** -/
theorem FreshSparsePhase.order_le_betaOf_rank
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) :
    F.data.order ≤ MainTheory.BetaExists.betaOf F.basis.rank :=
  FreshSparsePhase.order_le_of_betaBound_rank F
    (MainTheory.BetaExists.betaBound_betaOf _)

/-- **`beta_r <= beta_n`**, the second inequality of the same display. -/
theorem FreshSparsePhase.betaOf_rank_le_betaOf
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) :
    MainTheory.BetaExists.betaOf F.basis.rank
      ≤ MainTheory.BetaExists.betaOf n :=
  betaOf_mono F.rank_le_six

/-- **`q <= beta_r <= beta_n`**, the display of `eq:d3-full-bound`, at
arbitrary length.

`F.rank_le_six` is misnamed upstream -- it is `rank <= n` at every `n`, and the
six-qubit reading is the instance. -/
theorem FreshSparsePhase.order_le_betaOf_rank_le
    {c d : SS.State n ℂ} {theta : Fin n → ℝ}
    (F : FreshSparsePhase c d theta) :
    F.data.order ≤ MainTheory.BetaExists.betaOf F.basis.rank ∧
      MainTheory.BetaExists.betaOf F.basis.rank
        ≤ MainTheory.BetaExists.betaOf n :=
  ⟨FreshSparsePhase.order_le_betaOf_rank F,
    FreshSparsePhase.betaOf_rank_le_betaOf F⟩

end MainTheory.BetaAtPivotRank
