import MainTheory.ProvedWEUnion

/-!
# Properness of the orbit-8 interval, and the conjecture's right-hand side

Two clauses around `thm:six-WE-status` were stated and not proved.

`main.tex` says "Orbit 7 contains a full one-parameter enumerator interval,
orbit 8 contains a *proper* subinterval of that same line".  What existed was
`ProvedWEUnion.FI_half_subset`, an inclusion; properness is the half that
separates `W_8` from `W_7`, and it needs a witness in the difference.  The
witness is `L(0)`, and what makes it one is that `F_I` is injective -- it
reads its parameter off its own second coordinate, so no lemma about the other
six is needed.

And "Every proved nonempty image lies in the right-hand side of
`eq:global-WE-conjecture`".  The right-hand side there takes `M` on `[3/5, 1]`
while this development proves `M` only on `[2/3, 1]`, so the containment is an
interval inclusion, and stating it makes the relation between what is proved
and what is conjectured a theorem rather than a remark.

Note what is *not* claimed: the conjecture itself is about all exact
`((6,2,3))` codes, including the projectively trivial sector, and the paper is
explicit that resolving the four open orbit images would not prove it.
-/

namespace MainTheory.WEStrictInclusion

open MainTheory
open MainTheory.WImages

/-- `F_I` is injective: its second coordinate is the parameter. -/
theorem FI_injective : Function.Injective FI := by
  intro a b hab
  have h := congrFun hab 1
  simpa [FI] using h

/-- `L(0)` is not on the upper half of the line. -/
theorem FI_zero_not_mem_half : FI 0 ∉ FI '' Set.Icc (1 / 2 : ℝ) 1 := by
  rintro ⟨a, ha, hfa⟩
  have : a = 0 := FI_injective hfa
  rw [this] at ha
  norm_num at ha

/-- **Orbit 8's interval is a proper subinterval of orbit 7's.** -/
theorem FI_half_ssubset : FI '' Set.Icc (1 / 2 : ℝ) 1 ⊂ FI '' Set.Icc (0 : ℝ) 1 := by
  refine ⟨MainTheory.ProvedWEUnion.FI_half_subset, ?_⟩
  intro hsub
  exact FI_zero_not_mem_half (hsub (Set.mem_image_of_mem FI (by norm_num)))

/-! ## The conjecture's right-hand side -/

/-- The right-hand side of `eq:global-WE-conjecture`: the whole `L` line, the
`M` segment from `3/5`, and the isolated point. -/
noncomputable def conjecturedImages : Set (Fin 7 → ℝ) :=
  FI '' Set.Icc (0 : ℝ) 1 ∪ FII '' Set.Icc (3 / 5 : ℝ) 1 ∪ {WImages.R5A}

/-- **Every proved nonempty image lies in the conjecture's right-hand side.**

The only gap between the two is the `M` parameter range: this development
proves `[2/3, 1]` and the conjecture asserts `[3/5, 1]`. -/
theorem provedImages_subset_conjectured :
    MainTheory.ProvedWEUnion.provedImages ⊆ conjecturedImages := by
  rw [MainTheory.ProvedWEUnion.provedImages_eq, conjecturedImages]
  refine Set.union_subset_union_left _ (Set.union_subset_union_right _ ?_)
  refine Set.image_mono ?_
  intro t ht
  exact ⟨by linarith [ht.1], ht.2⟩

end MainTheory.WEStrictInclusion
