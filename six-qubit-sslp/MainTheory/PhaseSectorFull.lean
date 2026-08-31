import Mathlib
import SS.HilbertKL
import SixQubit.CodeBridge
import MainTheory.RealGate

/-!
# Phase sectors, including degenerate logical eigenspaces

This file formalizes the conclusions of Lemma 2.3 of
`documents/20260822/main.tex` once a finite logical eigenspace decomposition is
given.  A sector may have dimension greater than one.  Its probability is the
diagonal of the whole sector projector, divided by the sector rank:

`p_alpha(x) = rank(alpha)^(-1) * sum_r |psi_(alpha,r)(x)|^2`.

In particular, no individual eigenvector is substituted for a degenerate
sector projector.  The decomposition is deliberately supplied as data here.
`MainTheory.PhaseSectorBridge` packages the additional code-span completeness
condition and names the still-missing finite-dimensional spectral-extraction
principle.  Constructing that package from an arbitrary code-preserving
unitary is not claimed in this file.
-/

namespace MainTheory.PhaseSectorFull

open SS
open SixQubit

noncomputable section

variable {n t : ℕ} {theta : Fin n → ℝ}

/-- The unit complex number represented by a real phase modulo one. -/
noncomputable def phaseExp (phi : ℝ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (phi : ℂ))

/--
A supplied decomposition of a logical frame into eigensectors of the real
diagonal gate `D(theta)`.

The dependent index `Sigma alpha, Fin (rank alpha)` is an orthonormal logical
frame.  `rank_pos` rules out empty sectors, while `sectorCount_pos` rules out
the vacuous zero-sector decomposition.  Distinct sectors have distinct unitary
eigenvalues, although vectors inside one sector share that eigenvalue.
-/
structure SectorDecomposition (n t : ℕ) (theta : Fin n → ℝ) where
  sectorCount_pos : 0 < t
  rank : Fin t → ℕ
  rank_pos : ∀ alpha, 0 < rank alpha
  vec : (Σ alpha, Fin (rank alpha)) → SS.State n ℂ
  orthonormal : ∀ u v,
    SS.innerC (vec u) (vec v) = if u = v then 1 else 0
  phase : Fin t → ℝ
  phaseDistinct : Function.Injective (fun alpha => phaseExp (phase alpha))
  eigen : ∀ u,
    MainTheory.RealGate.realGate theta (vec u) =
      fun x => phaseExp (phase u.1) * vec u x

/-- The dependent logical-frame index carried by all sectors. -/
abbrev SectorDecomposition.Index (D : SectorDecomposition n t theta) :=
  Σ alpha, Fin (D.rank alpha)

/-- Matrix kernel of the orthogonal projector onto one logical eigensector. -/
noncomputable def sectorProjectorKernel (D : SectorDecomposition n t theta)
    (alpha : Fin t) (x y : SS.BitString n) : ℂ :=
  ∑ r : Fin (D.rank alpha),
    D.vec ⟨alpha, r⟩ x * star (D.vec ⟨alpha, r⟩ y)

/-- The diagonal entry `(R_alpha)_(x,x)` of the sector projector. -/
noncomputable def sectorProjectorDiag (D : SectorDecomposition n t theta)
    (alpha : Fin t) (x : SS.BitString n) : ℝ :=
  ∑ r : Fin (D.rank alpha), Complex.normSq (D.vec ⟨alpha, r⟩ x)

/-- The paper's normalized sector weight `(R_alpha)_(x,x) / rank(R_alpha)`. -/
noncomputable def sectorProbability (D : SectorDecomposition n t theta)
    (alpha : Fin t) (x : SS.BitString n) : ℝ :=
  sectorProjectorDiag D alpha x / (D.rank alpha : ℝ)

/-- The actual support of a sector projector. -/
def sectorSupport (D : SectorDecomposition n t theta) (alpha : Fin t) :
    Set (SS.BitString n) :=
  {x | 0 < sectorProbability D alpha x}

/-- A Boolean coordinate, embedded in the reals. -/
def coordinate (x : SS.BitString n) (j : Fin n) : ℝ :=
  if x j then 1 else 0

/-- The first moment of a normalized sector projector. -/
noncomputable def sectorMean (D : SectorDecomposition n t theta)
    (alpha : Fin t) (j : Fin n) : ℝ :=
  ∑ x, sectorProbability D alpha x * coordinate x j

/-- The exact `Z_j` Knill--Laflamme condition on the flattened logical frame. -/
def ZDetects (D : SectorDecomposition n t theta) : Prop :=
  ∀ j : Fin n, ∃ c : ℂ, ∀ u v : D.Index,
    SS.innerC (D.vec u)
      (SS.pauliAct (⟨fun _ => false, SS.stdBasis j⟩ : SS.PauliString n)
        (D.vec v)) = if u = v then c else 0

/-- Bridge from the repository's `Fin K`-indexed detection predicate.  The
equivalence says that the supplied sector vectors are just a reindexing of the
logical frame, rather than an unrelated auxiliary family. -/
theorem zDetects_of_detects_reindex {K : ℕ}
    (D : SectorDecomposition n t theta) (e : Fin K ≃ D.Index)
    (hdet : SS.Detects (fun k => D.vec (e k)) 1) : ZDetects D := by
  intro j
  let P : SS.PauliString n :=
    ⟨fun _ => false, SS.stdBasis j⟩
  have hwt : P.wt ≤ 1 := by
    simpa [P] using (wt_pureZ_single j)
  obtain ⟨c, hc⟩ := hdet P hwt
  refine ⟨c, ?_⟩
  intro u v
  have h := hc (e.symm u) (e.symm v)
  simpa [P] using h

/-- A distance-at-least-two code supplies the one-qubit `Z` equations required
by the phase-sector lemma. -/
theorem zDetects_of_hasDistance_reindex {K d : ℕ}
    (D : SectorDecomposition n t theta) (e : Fin K ≃ D.Index)
    (hdist : SS.HasDistance (fun k => D.vec (e k)) d) (hd : 2 ≤ d) :
    ZDetects D := by
  apply zDetects_of_detects_reindex D e
  intro P hP
  exact hdist P (by omega)

@[simp] theorem innerC_vec_self (D : SectorDecomposition n t theta)
    (u : D.Index) : SS.innerC (D.vec u) (D.vec u) = 1 := by
  simpa using D.orthonormal u u

/-- The real expression used for `sectorProbability` is exactly the diagonal
of the sector projector kernel. -/
theorem sectorProjectorKernel_diag (D : SectorDecomposition n t theta)
    (alpha : Fin t) (x : SS.BitString n) :
    sectorProjectorKernel D alpha x x = (sectorProjectorDiag D alpha x : ℂ) := by
  simp only [sectorProjectorKernel, sectorProjectorDiag, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Complex.normSq_eq_conj_mul_self]
  simp [mul_comm]

/-- Sector probabilities are pointwise nonnegative. -/
theorem sectorProbability_nonneg (D : SectorDecomposition n t theta)
    (alpha : Fin t) (x : SS.BitString n) :
    0 ≤ sectorProbability D alpha x := by
  apply div_nonneg
  · exact Finset.sum_nonneg fun r _ => Complex.normSq_nonneg _
  · exact_mod_cast (D.rank_pos alpha).le

/-- Every sector probability is normalized. -/
theorem sectorProbability_sum_eq_one (D : SectorDecomposition n t theta)
    (alpha : Fin t) :
    ∑ x, sectorProbability D alpha x = 1 := by
  have hmass : ∀ r : Fin (D.rank alpha),
      ∑ x : SS.BitString n, Complex.normSq (D.vec ⟨alpha, r⟩ x) = 1 := by
    intro r
    have h := massOn_eq_one
      (Finset.univ : Finset (SS.BitString n)) (D.vec ⟨alpha, r⟩)
      (by simp) (innerC_vec_self D ⟨alpha, r⟩)
    simpa [massOn] using h
  rw [show (∑ x, sectorProbability D alpha x) =
      (∑ x, ∑ r : Fin (D.rank alpha),
        Complex.normSq (D.vec ⟨alpha, r⟩ x)) / (D.rank alpha : ℝ) by
        simp only [sectorProbability, sectorProjectorDiag, Finset.sum_div]]
  rw [Finset.sum_comm]
  simp only [hmass, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact div_self (by exact_mod_cast (D.rank_pos alpha).ne')

/-- Membership in a sector support is witnessed by a nonzero amplitude of one
of the sector's orthonormal vectors. -/
theorem exists_vec_ne_zero_of_mem_support
    (D : SectorDecomposition n t theta) (alpha : Fin t)
    (x : SS.BitString n) (hx : x ∈ sectorSupport D alpha) :
    ∃ r : Fin (D.rank alpha), D.vec ⟨alpha, r⟩ x ≠ 0 := by
  by_contra h
  push_neg at h
  have hdiag : sectorProjectorDiag D alpha x = 0 := by
    simp [sectorProjectorDiag, h]
  have : sectorProbability D alpha x = 0 := by
    simp [sectorProbability, hdiag]
  exact (ne_of_gt hx) this

/-- Every positive-rank normalized sector has nonempty projector support. -/
theorem sectorSupport_nonempty (D : SectorDecomposition n t theta)
    (alpha : Fin t) : (sectorSupport D alpha).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hz : ∀ x : SS.BitString n, sectorProbability D alpha x = 0 := by
    intro x
    apply le_antisymm
    · have hx : x ∉ sectorSupport D alpha := by simp [h]
      exact not_lt.mp hx
    · exact sectorProbability_nonneg D alpha x
  have hsum := sectorProbability_sum_eq_one D alpha
  simp only [hz, Finset.sum_const_zero] at hsum
  norm_num at hsum

/-- Distinct logical eigensectors have disjoint computational support. -/
theorem sectorSupport_disjoint (D : SectorDecomposition n t theta)
    {alpha beta : Fin t} (hab : alpha ≠ beta) :
    Disjoint (sectorSupport D alpha) (sectorSupport D beta) := by
  rw [Set.disjoint_left]
  intro x hxa hxb
  obtain ⟨r, hr⟩ := exists_vec_ne_zero_of_mem_support D alpha x hxa
  obtain ⟨s, hs⟩ := exists_vec_ne_zero_of_mem_support D beta x hxb
  have hea := MainTheory.RealGate.exp_eq_of_eigen theta
    (D.vec ⟨alpha, r⟩) (phaseExp (D.phase alpha)) (D.eigen ⟨alpha, r⟩) x hr
  have heb := MainTheory.RealGate.exp_eq_of_eigen theta
    (D.vec ⟨beta, s⟩) (phaseExp (D.phase beta)) (D.eigen ⟨beta, s⟩) x hs
  exact hab (D.phaseDistinct (hea.symm.trans heb))

/-- The physical angle of every supported string agrees with the sector phase
modulo one. -/
theorem phase_congruence (D : SectorDecomposition n t theta)
    (alpha : Fin t) (x : SS.BitString n) (hx : x ∈ sectorSupport D alpha) :
    ∃ k : ℤ, MainTheory.RealGate.angle theta x - D.phase alpha = (k : ℝ) := by
  obtain ⟨r, hr⟩ := exists_vec_ne_zero_of_mem_support D alpha x hx
  have he := MainTheory.RealGate.exp_eq_of_eigen theta
    (D.vec ⟨alpha, r⟩) (phaseExp (D.phase alpha)) (D.eigen ⟨alpha, r⟩) x hr
  have hquot : Complex.exp
      (2 * (Real.pi : ℂ) * Complex.I *
        ((MainTheory.RealGate.angle theta x - D.phase alpha : ℝ) : ℂ)) = 1 := by
    push_cast
    rw [mul_sub, Complex.exp_sub, he]
    exact div_self (Complex.exp_ne_zero _)
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hquot
  refine ⟨k, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcoef : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero
  have hk' : (2 : ℂ) * (Real.pi : ℂ) * Complex.I *
        ((MainTheory.RealGate.angle theta x - D.phase alpha : ℝ) : ℂ) =
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I * (k : ℂ) := by
    rw [hk]
    ring
  exact_mod_cast mul_left_cancel₀ hcoef hk'

/-- The sector mean is the average of the occupation means of an orthonormal
basis of that sector. -/
theorem sectorMean_eq_average_occOn (D : SectorDecomposition n t theta)
    (alpha : Fin t) (j : Fin n) :
    sectorMean D alpha j =
      (∑ r : Fin (D.rank alpha),
        occOn Finset.univ (D.vec ⟨alpha, r⟩) j) / (D.rank alpha : ℝ) := by
  simp only [sectorMean, sectorProbability, sectorProjectorDiag, coordinate]
  calc
    (∑ x, (∑ r : Fin (D.rank alpha),
          Complex.normSq (D.vec ⟨alpha, r⟩ x)) / (D.rank alpha : ℝ) *
        (if x j then 1 else 0)) =
        ∑ x, (∑ r : Fin (D.rank alpha),
          Complex.normSq (D.vec ⟨alpha, r⟩ x) *
            (if x j then 1 else 0)) / (D.rank alpha : ℝ) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← Finset.sum_mul]
          ring
    _ = (∑ x, ∑ r : Fin (D.rank alpha),
          Complex.normSq (D.vec ⟨alpha, r⟩ x) *
            (if x j then 1 else 0)) / (D.rank alpha : ℝ) := by
          rw [Finset.sum_div]
    _ = (∑ r : Fin (D.rank alpha), ∑ x,
          Complex.normSq (D.vec ⟨alpha, r⟩ x) *
            (if x j then 1 else 0)) / (D.rank alpha : ℝ) := by
          rw [Finset.sum_comm]
    _ = (∑ r : Fin (D.rank alpha),
          occOn Finset.univ (D.vec ⟨alpha, r⟩) j) /
            (D.rank alpha : ℝ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro r _
          rw [occOn, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x j <;> simp [hx]

private theorem occOn_eq_of_ZDetects (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (u v : D.Index) (j : Fin n) :
    occOn Finset.univ (D.vec u) j = occOn Finset.univ (D.vec v) j := by
  obtain ⟨c, hc⟩ := hZ j
  have huu := hc u u
  have hvv := hc v v
  rw [if_pos rfl] at huu hvv
  have hu_char := innerC_pureZ_eq_charOn
    (Finset.univ : Finset (SS.BitString n)) (D.vec u) (by simp)
    (SS.stdBasis j)
  have hv_char := innerC_pureZ_eq_charOn
    (Finset.univ : Finset (SS.BitString n)) (D.vec v) (by simp)
    (SS.stdBasis j)
  change SS.innerC (D.vec u)
      (SS.pauliAct (⟨fun _ => false, SS.stdBasis j⟩ : SS.PauliString n)
        (D.vec u)) = ((charOn Finset.univ (D.vec u) (SS.stdBasis j) : ℝ) : ℂ)
    at hu_char
  change SS.innerC (D.vec v)
      (SS.pauliAct (⟨fun _ => false, SS.stdBasis j⟩ : SS.PauliString n)
        (D.vec v)) = ((charOn Finset.univ (D.vec v) (SS.stdBasis j) : ℝ) : ℂ)
    at hv_char
  have hchar : charOn Finset.univ (D.vec u) (SS.stdBasis j) =
      charOn Finset.univ (D.vec v) (SS.stdBasis j) := by
    exact_mod_cast (show
      ((charOn Finset.univ (D.vec u) (SS.stdBasis j) : ℝ) : ℂ) =
        ((charOn Finset.univ (D.vec v) (SS.stdBasis j) : ℝ) : ℂ) by
      rw [← hu_char, ← hv_char, huu, hvv])
  have hmassu := massOn_eq_one
    (Finset.univ : Finset (SS.BitString n)) (D.vec u) (by simp)
    (innerC_vec_self D u)
  have hmassv := massOn_eq_one
    (Finset.univ : Finset (SS.BitString n)) (D.vec v) (by simp)
    (innerC_vec_self D v)
  rw [charOn_stdBasis, charOn_stdBasis, hmassu, hmassv] at hchar
  linarith

/-- Exact `Z_j` KL detection makes all sector projector means equal. -/
theorem sectorMean_eq_of_ZDetects (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) (alpha beta : Fin t) (j : Fin n) :
    sectorMean D alpha j = sectorMean D beta j := by
  let u0 : D.Index := ⟨alpha, ⟨0, D.rank_pos alpha⟩⟩
  have havg (gamma : Fin t) :
      (∑ r : Fin (D.rank gamma), occOn Finset.univ (D.vec ⟨gamma, r⟩) j) /
          (D.rank gamma : ℝ) = occOn Finset.univ (D.vec u0) j := by
    have heq : ∀ r : Fin (D.rank gamma),
        occOn Finset.univ (D.vec ⟨gamma, r⟩) j =
          occOn Finset.univ (D.vec u0) j := by
      intro r
      exact occOn_eq_of_ZDetects D hZ ⟨gamma, r⟩ u0 j
    simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    exact (mul_div_cancel_left₀ _ (by exact_mod_cast (D.rank_pos gamma).ne'))
  rw [sectorMean_eq_average_occOn, sectorMean_eq_average_occOn,
    havg alpha, havg beta]

/-- Vector form of the common-first-moment conclusion. -/
theorem exists_common_sector_mean (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) :
    ∃ mu : Fin n → ℝ, ∀ alpha j, sectorMean D alpha j = mu j := by
  let alpha0 : Fin t := ⟨0, D.sectorCount_pos⟩
  refine ⟨sectorMean D alpha0, ?_⟩
  intro alpha j
  exact sectorMean_eq_of_ZDetects D hZ alpha alpha0 j

/--
**Full phase-sector package, conditional only on the supplied eigenspace
decomposition.**

This is the collection of conclusions in Lemma 2.3: each projector-average
weight is a probability distribution with nonempty support; distinct sectors
are disjoint; every supported basis string has the prescribed phase modulo
one; and exact one-qubit `Z` KL equations give one common first-moment vector.
-/
theorem phaseSectorFull_package (D : SectorDecomposition n t theta)
    (hZ : ZDetects D) :
    (∀ alpha x, 0 ≤ sectorProbability D alpha x) ∧
    (∀ alpha, ∑ x, sectorProbability D alpha x = 1) ∧
    (∀ alpha, (sectorSupport D alpha).Nonempty) ∧
    (∀ alpha beta, alpha ≠ beta →
      Disjoint (sectorSupport D alpha) (sectorSupport D beta)) ∧
    (∀ alpha x, x ∈ sectorSupport D alpha →
      ∃ k : ℤ, MainTheory.RealGate.angle theta x - D.phase alpha = (k : ℝ)) ∧
    ∃ mu : Fin n → ℝ, ∀ alpha j, sectorMean D alpha j = mu j := by
  exact ⟨sectorProbability_nonneg D, sectorProbability_sum_eq_one D,
    sectorSupport_nonempty D, fun _ _ => sectorSupport_disjoint D,
    phase_congruence D, exists_common_sector_mean D hZ⟩

/-- Paper-facing wrapper: the full package follows from a distance-at-least-two
logical frame reindexed by the supplied sector decomposition. -/
theorem phaseSectorFull_package_of_hasDistance {K d : ℕ}
    (D : SectorDecomposition n t theta) (e : Fin K ≃ D.Index)
    (hdist : SS.HasDistance (fun k => D.vec (e k)) d) (hd : 2 ≤ d) :
    (∀ alpha x, 0 ≤ sectorProbability D alpha x) ∧
    (∀ alpha, ∑ x, sectorProbability D alpha x = 1) ∧
    (∀ alpha, (sectorSupport D alpha).Nonempty) ∧
    (∀ alpha beta, alpha ≠ beta →
      Disjoint (sectorSupport D alpha) (sectorSupport D beta)) ∧
    (∀ alpha x, x ∈ sectorSupport D alpha →
      ∃ k : ℤ, MainTheory.RealGate.angle theta x - D.phase alpha = (k : ℝ)) ∧
    ∃ mu : Fin n → ℝ, ∀ alpha j, sectorMean D alpha j = mu j :=
  phaseSectorFull_package D (zDetects_of_hasDistance_reindex D e hdist hd)

end

end MainTheory.PhaseSectorFull
