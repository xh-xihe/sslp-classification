import MainTheory.QubitTransversalFinite

/-! # The Eastin--Knill no-universality theorem

This is `main.tex`'s unlabelled Theorem "Eastin--Knill no-go theorem": a
nontrivial finite-dimensional quantum code that detects every error acting on
any one physical subsystem admits no universal set of logical unitaries
implemented entirely by transversal physical unitaries.  The manuscript gives
that theorem no `\label`, so it is cited here by its title.

`eastin_knill` is the statement at arbitrary finite subsystem dimensions and
`eastin_knill_exactCode` applies it to this repository's exact qubit codes
through their genuine Pauli Knill--Laflamme distance predicate.

Universality is stated in the ordinary matrix topology on the faithful
adjoint action: every projective logical unitary must be approximable by
implemented transversal logical unitaries.  The physical transversal image
is finite, whereas the full projective unitary image contains a copy of the
circle whenever the code rank is at least two.
-/

namespace MainTheory.EastinKnill

open UnitaryAdjointRepresentation FiniteTensorDetection TransversalLogicalOrder

noncomputable section

variable {L : Type*} [Fintype L] [DecidableEq L]

set_option linter.unusedSectionVars false

def phaseUnitary (i : L) (z : Circle) : Matrix.unitaryGroup L ℂ :=
  ⟨Matrix.diagonal (fun k => if k = i then (z : ℂ) else 1), by
    apply Matrix.mem_unitaryGroup_iff'.2
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    change Matrix.diagonal (fun k => star (if k = i then (z : ℂ) else 1) *
      (if k = i then (z : ℂ) else 1)) = 1
    rw [← Matrix.diagonal_one]
    apply congrArg Matrix.diagonal
    funext k
    by_cases hk : k = i
    · simp only [if_pos hk]
      have h := congrArg (fun r : ℝ => (r : ℂ)) (Circle.normSq_coe z)
      simpa only [Complex.normSq_eq_conj_mul_self, Complex.ofReal_one] using h
    · simp [hk]⟩

theorem phase_adjoint_injective (i j : L) (hij : i ≠ j) :
    Function.Injective (fun z : Circle => adjoint (phaseUnitary i z)) := by
  intro z w h
  apply Circle.ext
  have he := congrArg (fun U : Matrix.unitaryGroup (L × L) ℂ => U.val (i, j) (i, j)) h
  simpa [adjoint_entry, phaseUnitary, Ne.symm hij] using he

theorem projective_unitary_image_infinite (i j : L) (hij : i ≠ j) :
    (Set.range (adjoint (L := L))).Infinite := by
  letI : Infinite (Set.Ioc (-Real.pi) Real.pi) := Set.Ioc.infinite (by linarith [Real.pi_pos])
  letI : Infinite Circle := Infinite.of_injective Circle.argEquiv.symm Circle.argEquiv.symm.injective
  have h := Set.infinite_range_of_injective (phase_adjoint_injective i j hij)
  apply h.mono
  rintro _ ⟨z, rfl⟩
  exact ⟨phaseUnitary i z, rfl⟩

/-- Density modulo global phase, expressed through its faithful action on
all logical operators, in the standard finite-dimensional matrix topology. -/
def ProjectivelyUniversal (G : Subgroup (Matrix.unitaryGroup L ℂ)) : Prop :=
  Set.range (adjoint (L := L)) ⊆
    closure ((G.map adjoint : Subgroup (Matrix.unitaryGroup (L × L) ℂ)) : Set _)

theorem not_universal_of_finite_projective_image
    (G : Subgroup (Matrix.unitaryGroup L ℂ)) [Finite (G.map adjoint)]
    (i j : L) (hij : i ≠ j) : ¬ ProjectivelyUniversal G := by
  have hfinite : (SetLike.coe (G.map adjoint)).Finite := Set.toFinite _
  intro h
  have hsub : Set.range (adjoint (L := L)) ⊆ SetLike.coe (G.map adjoint) := by
    simpa only [ProjectivelyUniversal, hfinite.isClosed.closure_eq] using h
  exact projective_unitary_image_infinite i j hij (hfinite.subset hsub)

/-- **Eastin--Knill.**  A finite-dimensional code of rank at least two that
detects every error on each physical subsystem has no universal collection
of transversal logical unitaries.  Physical subsystem dimensions may be
arbitrary, different finite dimensions. -/
theorem eastin_knill
    {S : Type*} [Fintype S] [DecidableEq S] {A : S → Type*}
    [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] {K : ℕ}
    (V : Matrix (∀ j, A j) (Fin K) ℂ) (hV : V.conjTranspose * V = 1)
    (hK : 2 ≤ K) (hdet : DetectsLocal V) :
    ¬ ProjectivelyUniversal (transversalLogicalGroup V) := by
  letI := finite_projective_transversal_image V hV (by omega) hdet
  exact not_universal_of_finite_projective_image (transversalLogicalGroup V)
    (⟨0, by omega⟩ : Fin K) ⟨1, by omega⟩ (by simp [Fin.ext_iff])

/-- The theorem applied directly to the repository's exact qubit codes and
their genuine Pauli KL distance predicate. -/
theorem eastin_knill_exactCode {n K d : ℕ} (C : CodeSpec.ExactCode n K d)
    (hK : 2 ≤ K) (hd : 2 ≤ d) :
    ¬ ProjectivelyUniversal (transversalLogicalGroup (A := fun _ : Fin n => Bool)
      (PauliKernelBTrace.frameMatrix C.frame)) :=
  eastin_knill (PauliKernelBTrace.frameMatrix C.frame) (KLCodeBridge.frameMatrix_gram C.frame)
    hK (QubitTransversalFinite.detectsLocal_of_hasDistance C hd)

end

end MainTheory.EastinKnill
