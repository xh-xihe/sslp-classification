import MainTheory.CubeCompletionTransport
import SixQubit.CodeEquivEnum

/-!
# Actual enumerator images of fibre orbits

The image is defined using normalized quantum states and the full KL predicate.
Transport preserves every enumerator coordinate, not only completion existence.
Thus a literal representative theorem determines the image of its whole cube
orbit, including completions with zero amplitudes.
-/

namespace MainTheory.EnumeratorOrbitTransport

open MainTheory.CubeAction MainTheory.CubeCompletionTransport

noncomputable section

/-- Normalized enumerators of actual distance-three completions on a pair. -/
def completionImage (F : FiberPair 6) : Set (Fin 7 → ℝ) :=
  {A | ∃ W : Completion F, ∀ j, A j = SS.MacWilliams.Aco W.states j / 4}

theorem completionImage_eq_empty_of_noCompletion {F : FiberPair 6}
    (hF : NoCompletion F) : completionImage F = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro A ⟨W, _⟩
  exact hF ⟨W⟩

theorem Aco_pushCompletion {F : FiberPair 6} (W : Completion F)
    (g : Parameter 6) (j : ℕ) :
    SS.MacWilliams.Aco (pushCompletion W g).states j =
      SS.MacWilliams.Aco W.states j := by
  exact SixQubit.CodeEquiv.Aco_fixed_perm_flip_swap
    g.perm.symm g.shift W.states g.swap j

theorem Bco_pushCompletion {F : FiberPair 6} (W : Completion F)
    (g : Parameter 6) (j : ℕ) :
    SS.MacWilliams.Bco (pushCompletion W g).states j =
      SS.MacWilliams.Bco W.states j := by
  exact SixQubit.CodeEquiv.Bco_fixed_perm_flip_swap
    g.perm.symm g.shift W.states g.swap j

theorem completionImage_actFibers (g : Parameter 6) (F : FiberPair 6) :
    completionImage (actFibers g F) = completionImage F := by
  ext A
  constructor
  · rintro ⟨W, hW⟩
    have hm : A ∈ completionImage (actFibers (inv g) (actFibers g F)) := by
      refine ⟨pushCompletion W (inv g), fun j => ?_⟩
      rw [Aco_pushCompletion]
      exact hW j
    simpa using hm
  · rintro ⟨W, hW⟩
    refine ⟨pushCompletion W g, fun j => ?_⟩
    rw [Aco_pushCompletion]
    exact hW j

theorem completionImage_eq_of_fiberEquivalent {F G : FiberPair 6}
    (h : FiberEquivalent F G) : completionImage G = completionImage F := by
  obtain ⟨g, rfl⟩ := h
  exact completionImage_actFibers g F

/-- All completions on all representatives of a cube orbit. -/
def orbitImage (F : FiberPair 6) : Set (Fin 7 → ℝ) :=
  {A | ∃ G, FiberEquivalent F G ∧ A ∈ completionImage G}

theorem orbitImage_eq_completionImage (F : FiberPair 6) :
    orbitImage F = completionImage F := by
  ext A
  constructor
  · rintro ⟨G, hFG, hA⟩
    rwa [completionImage_eq_of_fiberEquivalent hFG] at hA
  · intro hA
    exact ⟨F, fiberEquivalent_refl F, hA⟩

/-- The paper's literal-fibre image and the class-level image use exactly the
same states, normalization and full KL predicate. -/
theorem WImage_eq_completionImage {q : ℕ} [NeZero q]
    (av : Fin 6 → ZMod q) (r0 r1 : ZMod q) (F : FiberPair 6)
    (hF0 : Finset.univ.filter (fun x => SS.weight av x = r0) = F false)
    (hF1 : Finset.univ.filter (fun x => SS.weight av x = r1) = F true) :
    MainTheory.Levels.WImage av r0 r1 = completionImage F := by
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    refine ⟨⟨![c, d], ?_, ?_, hdist⟩, hA⟩
    · intro k x hx
      fin_cases k
      · apply hc x
        intro heq
        apply hx
        change x ∈ F false
        rw [← hF0]
        simp [heq]
      · apply hd x
        intro heq
        apply hx
        change x ∈ F true
        rw [← hF1]
        simp [heq]
    · intro k
      fin_cases k
      · exact hnc
      · exact hnd
  · rintro ⟨W, hA⟩
    have hp : ![W.states 0, W.states 1] = W.states := by
      funext k
      fin_cases k <;> rfl
    refine ⟨W.states 0, W.states 1, ?_, ?_, W.normalized 0,
      W.normalized 1, ?_, ?_⟩
    · intro x hx
      apply W.supported 0 x
      change x ∉ F false
      rw [← hF0]
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
    · intro x hx
      apply W.supported 1 x
      change x ∉ F true
      rw [← hF1]
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
    · rw [hp]
      exact W.hasDistance
    · intro j
      rw [hp]
      exact hA j

theorem WImage_eq_orbitImage {q : ℕ} [NeZero q]
    (av : Fin 6 → ZMod q) (r0 r1 : ZMod q) (F : FiberPair 6)
    (hF0 : Finset.univ.filter (fun x => SS.weight av x = r0) = F false)
    (hF1 : Finset.univ.filter (fun x => SS.weight av x = r1) = F true) :
    MainTheory.Levels.WImage av r0 r1 = orbitImage F := by
  rw [orbitImage_eq_completionImage]
  exact WImage_eq_completionImage av r0 r1 F hF0 hF1

end

end MainTheory.EnumeratorOrbitTransport
