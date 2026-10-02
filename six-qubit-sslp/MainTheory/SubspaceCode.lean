import MainTheory.GeneralColoredSubspaces
import MainTheory.FrameDistanceOne

/-! # Orthonormal frames and KL certification for arbitrary subspaces

The state type uses the coordinatewise norm, so orthonormal bases are chosen
in its Euclidean realization and transported back by the linear equivalence.
The resulting frame spans exactly the supplied subspace, including rank zero.
-/

namespace MainTheory.SubspaceCode

open CodeSpec

noncomputable section

variable {n K d : ℕ}

def euclideanSpace (E : Submodule ℂ (SS.State n ℂ)) :
    Submodule ℂ (EuclideanSpace ℂ (SS.BitString n)) :=
  E.map (GeneralSpectral.stateEquiv n).toLinearMap

theorem finrank_euclideanSpace (E : Submodule ℂ (SS.State n ℂ)) :
    Module.finrank ℂ (euclideanSpace E) = Module.finrank ℂ E :=
  (GeneralSpectral.stateEquiv n).finrank_map_eq E

def euclideanBasis (E : Submodule ℂ (SS.State n ℂ))
    (hE : Module.finrank ℂ E = K) :
    OrthonormalBasis (Fin K) ℂ (euclideanSpace E) :=
  (stdOrthonormalBasis ℂ (euclideanSpace E)).reindex
    (finCongr ((finrank_euclideanSpace E).trans hE))

def frame (E : Submodule ℂ (SS.State n ℂ))
    (hE : Module.finrank ℂ E = K) : OrthonormalFrame n K where
  vec i := (GeneralSpectral.stateEquiv n).symm (euclideanBasis E hE i)
  orthonormal i j := by
    rw [StateEuclidean.innerC_eq_inner]
    change inner ℂ ((euclideanBasis E hE i).val) ((euclideanBasis E hE j).val) = _
    exact (euclideanBasis E hE).inner_eq_ite i j

theorem frame_mem (E : Submodule ℂ (SS.State n ℂ))
    (hE : Module.finrank ℂ E = K) (i : Fin K) : (frame E hE).vec i ∈ E := by
  obtain ⟨x, hx, heq⟩ := (euclideanBasis E hE i).property
  change (GeneralSpectral.stateEquiv n).symm _ ∈ E
  rw [← heq]
  exact hx

theorem codeSpan_frame (E : Submodule ℂ (SS.State n ℂ))
    (hE : Module.finrank ℂ E = K) : codeSpan (frame E hE) = E := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact frame_mem E hE i
  · exact (GeneralColoredSubspaces.finrank_codeSpan _).trans hE.symm

/-- Basis-independent KL on precisely the Paulis of weight strictly below `d`. -/
def HasDistance (E : Submodule ℂ (SS.State n ℂ)) (d : ℕ) : Prop :=
  ∀ P : SS.PauliString n, P.wt < d →
    ∃ c : ℂ, ∀ psi, psi ∈ E → ∀ phi, phi ∈ E →
      SS.innerC psi (SS.pauliAct P phi) = c * SS.innerC psi phi

theorem hasDistance_iff (F : OrthonormalFrame n K) :
    HasDistance (codeSpan F) d ↔ SS.HasDistance F.vec d := by
  classical
  constructor
  · intro h P hP
    by_cases hd : d = 0
    · subst d
      exact FrameDistanceOne.hasDistance_one F P hP
    · obtain ⟨c, hc⟩ := h P (by omega)
      refine ⟨c, fun i j => ?_⟩
      rw [hc (F.vec i) (Submodule.subset_span (Set.mem_range_self i))
        (F.vec j) (Submodule.subset_span (Set.mem_range_self j)), F.orthonormal]
      by_cases hij : i = j <;> simp [hij]
  · intro h P hP
    exact scalarCompression_of_klCondition F P (h P (by omega))

theorem frame_hasDistance (E : Submodule ℂ (SS.State n ℂ))
    (hE : Module.finrank ℂ E = K) (h : HasDistance E d) :
    SS.HasDistance (frame E hE).vec d := by
  apply (hasDistance_iff _).1
  simpa only [codeSpan_frame] using h

end

end MainTheory.SubspaceCode
