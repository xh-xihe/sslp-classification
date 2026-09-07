import Mathlib

/-!
# `lem:connected-orthogonality`

The supplementary manuscript's order-two argument runs on a rigidity lemma
about a connected bipartite graph carrying nonzero vectors of `C^2`:
if the two sides are orthogonal along every edge, then all left vectors lie
on one line and all right vectors on its orthogonal line, and consequently
the two frame operators cannot be equal.

Nothing in the repository proved it.  The nearest declaration,
`SixQubit.ParityFour.slice_zero`, concludes a mass identity rather than the
existence of the line, so it is not a counterpart.  This file proves the
lemma.

Two choices are worth stating.

* The graph is carried as a relation together with an explicit reachability
  hypothesis rather than as a `SimpleGraph` on a sum type.  "Connected
  bipartite graph" is used for exactly one thing in the proof -- being able
  to walk from a base left vertex to any other left vertex through shared
  right neighbours -- and `hconn` says precisely that, with `hcover` saying
  every right vertex has a neighbour.  Stating the hypothesis this way keeps
  it checkable against the manuscript and keeps the lemma usable wherever a
  connectivity fact is already available in whatever form.
* The ambient space is any complex inner product space of dimension two,
  not `EuclideanSpace C (Fin 2)` specifically.  The manuscript's `C^2` is an
  instance.

The frame-operator conclusion is proved without the manuscript's hypothesis
that the two sides carry the same positive total mass.  That hypothesis lets
the manuscript display the two operators as `mu * P_L` and `mu * P_Lperp`;
the inequality itself does not need it, since the left frame is already
nonzero on `c x0` while the right frame annihilates it.  A stronger
conclusion from fewer hypotheses is recorded rather than the weaker one.
-/

namespace MainTheory.ConnectedOrthogonality

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The two-dimensional step.**

In a two-dimensional space the orthogonal complement of a nonzero vector is a
line, so two vectors orthogonal to the same nonzero vector are parallel --
this is the sentence "in `C^2`, the orthogonal complement of a nonzero vector
is one-dimensional" that the manuscript's proof turns on. -/
theorem mem_span_of_inner_eq_zero [FiniteDimensional ℂ E]
    (hdim : Module.finrank ℂ E = 2) {c c' d : E} (hd : d ≠ 0) (hc : c ≠ 0)
    (h : ⟪c, d⟫_ℂ = 0) (h' : ⟪c', d⟫_ℂ = 0) :
    c' ∈ (ℂ ∙ c) := by
  have hcmem : c ∈ (ℂ ∙ d)ᗮ := Submodule.mem_orthogonal_singleton_iff_inner_left.2 h
  have hle : (ℂ ∙ c) ≤ (ℂ ∙ d)ᗮ := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hcmem
  have hone : Module.finrank ℂ (ℂ ∙ c) = 1 := finrank_span_singleton hc
  have hdone : Module.finrank ℂ (ℂ ∙ d) = 1 := finrank_span_singleton hd
  have hsum := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℂ) (K := (ℂ ∙ d))
  have hperp : Module.finrank ℂ ((ℂ ∙ d)ᗮ) = 1 := by
    rw [hdone, hdim] at hsum
    omega
  have heq : (ℂ ∙ c) = (ℂ ∙ d)ᗮ :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hone, hperp])
  rw [heq]
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 h'

/-- **`lem:connected-orthogonality`, the line.**

`adj` is the edge relation of the bipartite graph, `hconn` says every left
vertex is reachable from `x0` by steps through a shared right neighbour, and
`hcover` says every right vertex has a left neighbour.  Together these are
connectedness of the bipartite graph, used for nothing else.

The conclusion is the manuscript's: a line `L` containing every `c x`, with
every `d y` in `L` perp. -/
theorem exists_line {V W : Type*} [FiniteDimensional ℂ E]
    (hdim : Module.finrank ℂ E = 2)
    (c : V → E) (d : W → E) (adj : V → W → Prop)
    (hc : ∀ x, c x ≠ 0) (hd : ∀ y, d y ≠ 0)
    (horth : ∀ x y, adj x y → ⟪c x, d y⟫_ℂ = 0)
    (x0 : V)
    (hconn : ∀ x, Relation.ReflTransGen
      (fun a b : V => ∃ y, adj a y ∧ adj b y) x0 x)
    (hcover : ∀ y, ∃ x, adj x y) :
    ∃ L : Submodule ℂ E, Module.finrank ℂ L = 1 ∧
      (∀ x, c x ∈ L) ∧ (∀ y, d y ∈ Lᗮ) := by
  -- Propagate along the graph: each step keeps the left vector on the line.
  have hline : ∀ x, c x ∈ (ℂ ∙ c x0) := by
    intro x
    induction hconn x with
    | refl => exact Submodule.mem_span_singleton_self _
    | tail _ hstep ih =>
        obtain ⟨y, hay, hby⟩ := hstep
        rename_i a b _
        have hmem : c b ∈ (ℂ ∙ c a) :=
          mem_span_of_inner_eq_zero hdim (hd y) (hc a) (horth a y hay) (horth b y hby)
        have hsub : (ℂ ∙ c a) ≤ (ℂ ∙ c x0) := by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact ih
        exact hsub hmem
  refine ⟨ℂ ∙ c x0, finrank_span_singleton (hc x0), hline, ?_⟩
  -- Every right vertex is orthogonal to the line, through any neighbour.
  intro y
  obtain ⟨x, hxy⟩ := hcover y
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (hline x)
  have hne : t ≠ 0 := by
    intro h
    apply hc x
    rw [← ht, h, zero_smul]
  have hzero : ⟪c x, d y⟫_ℂ = 0 := horth x y hxy
  rw [← ht, inner_smul_left] at hzero
  have hkey : ⟪c x0, d y⟫_ℂ = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd (star_eq_zero.1 h) hne
    · exact h
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 hkey

/-- **`lem:connected-orthogonality`, the frame consequence.**

The two frame operators disagree: there is a test vector on which the left
quadratic form is nonzero while the right one vanishes.

The manuscript adds the hypothesis that the two sides carry the same positive
total mass, in order to display the operators as `mu * P_L` and
`mu * P_Lperp`.  The inequality does not need it -- `c x0` alone already
separates the two forms -- so it is not assumed here. -/
theorem frame_forms_ne {V W : Type*} [Fintype V] [Fintype W]
    [FiniteDimensional ℂ E]
    (hdim : Module.finrank ℂ E = 2)
    (c : V → E) (d : W → E) (adj : V → W → Prop)
    (hc : ∀ x, c x ≠ 0) (hd : ∀ y, d y ≠ 0)
    (horth : ∀ x y, adj x y → ⟪c x, d y⟫_ℂ = 0)
    (x0 : V)
    (hconn : ∀ x, Relation.ReflTransGen
      (fun a b : V => ∃ y, adj a y ∧ adj b y) x0 x)
    (hcover : ∀ y, ∃ x, adj x y) :
    ∃ v : E, (∑ x, ‖⟪c x, v⟫_ℂ‖ ^ 2) ≠ (∑ y, ‖⟪d y, v⟫_ℂ‖ ^ 2) := by
  obtain ⟨L, _, hcL, hdL⟩ :=
    exists_line hdim c d adj hc hd horth x0 hconn hcover
  refine ⟨c x0, ?_⟩
  have hright : (∑ y, ‖⟪d y, c x0⟫_ℂ‖ ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun y _ => ?_
    have : ⟪d y, c x0⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (hcL x0) (hdL y)
    rw [this]
    simp
  have hpos : 0 < ∑ x, ‖⟪c x, c x0⟫_ℂ‖ ^ 2 := by
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨x0, Finset.mem_univ _, ?_⟩
    have hne : ⟪c x0, c x0⟫_ℂ ≠ 0 := inner_self_ne_zero.2 (hc x0)
    positivity
  rw [hright]
  exact ne_of_gt hpos

end MainTheory.ConnectedOrthogonality
