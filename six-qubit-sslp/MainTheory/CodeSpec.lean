import Mathlib
import SS.HilbertKL
import SixQubit.MacWilliams
import SixQubit.BEnumerator

/-!
# Code, projector, and normalized-enumerator semantics

This file gives the general theory a small semantic layer that is independent
of any SSLP presentation.  An `OrthonormalFrame n K` is an ordered orthonormal
logical frame in the `n`-qubit Hilbert space, and an `ExactCode n K d` is such
a frame satisfying the genuine Knill--Laflamme predicate `SS.HasDistance`.

The frame determines its orthogonal projector both by a matrix kernel and by
its action on states.  The results below prove the characteristic identities
directly: the projector fixes every frame vector, is idempotent, and has a
Hermitian kernel.

Finally, `AWeight` and `BWeight` use the normalization of `main.tex`, rather
than the repository's historical unnormalized coefficients.  A generic
restricted image is provided only as an auxiliary construction; it is not
identified with a paper orbit until a concrete orbit predicate is supplied.
-/

namespace MainTheory.CodeSpec

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ## Exact codes -/

/-- An ordered orthonormal logical frame in the `n`-qubit Hilbert space. -/
structure OrthonormalFrame (n K : ℕ) where
  vec : Fin K → SS.State n ℂ
  orthonormal : ∀ i j, SS.innerC (vec i) (vec j) = if i = j then 1 else 0

/-- An exact `((n,K,d))` code, presented by an orthonormal logical frame and
the genuine Knill--Laflamme distance predicate. -/
structure ExactCode (n K d : ℕ) where
  /-- Codes have positive logical rank.  Keeping this in the structure blocks
  the vacuous `K = 0` model, in which every frame-indexed condition is true. -/
  positiveRank : 0 < K
  frame : OrthonormalFrame n K
  hasDistance : SS.HasDistance frame.vec d

/-- Regression guard: the empty logical frame cannot masquerade as an exact
code by making every indexed condition vacuous. -/
theorem exactCode_rank_zero_isEmpty (n d : ℕ) : IsEmpty (ExactCode n 0 d) :=
  ⟨fun C => Nat.not_lt_zero _ C.positiveRank⟩

/-! ## The frame projector -/

/-- Matrix kernel of the orthogonal projector onto the span of a frame. -/
def projectorKernel {n K : ℕ} (F : OrthonormalFrame n K)
    (x y : SS.BitString n) : ℂ :=
  ∑ k, F.vec k x * star (F.vec k y)

/-- Action of the frame projector, written in bra--ket form. -/
def projectorAction {n K : ℕ} (F : OrthonormalFrame n K)
    (phi : SS.State n ℂ) : SS.State n ℂ :=
  fun x => ∑ k, F.vec k x * SS.innerC (F.vec k) phi

/-- The bra--ket action is exactly multiplication by `projectorKernel`. -/
theorem projectorAction_eq_kernel {n K : ℕ} (F : OrthonormalFrame n K)
    (phi : SS.State n ℂ) (x : SS.BitString n) :
    projectorAction F phi x = ∑ y, projectorKernel F x y * phi y := by
  classical
  simp only [projectorAction, projectorKernel, SS.innerC, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun y _ => by ring

/-- The projector fixes every vector of its defining orthonormal frame. -/
@[simp] theorem projectorAction_vec {n K : ℕ} (F : OrthonormalFrame n K)
    (j : Fin K) : projectorAction F (F.vec j) = F.vec j := by
  classical
  funext x
  simp [projectorAction, F.orthonormal]

/-- Taking the inner product with a frame vector is unchanged by projection. -/
theorem innerC_projectorAction {n K : ℕ} (F : OrthonormalFrame n K)
    (j : Fin K) (phi : SS.State n ℂ) :
    SS.innerC (F.vec j) (projectorAction F phi) = SS.innerC (F.vec j) phi := by
  classical
  rw [SS.innerC]
  simp only [projectorAction, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ k : Fin K, ∑ x : SS.BitString n,
        star (F.vec j x) * (F.vec k x * SS.innerC (F.vec k) phi)) =
        ∑ k : Fin K, SS.innerC (F.vec j) (F.vec k) *
          SS.innerC (F.vec k) phi := by
            apply Finset.sum_congr rfl
            intro k _
            simp only [SS.innerC]
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun x _ => by ring
    _ = SS.innerC (F.vec j) phi := by simp [F.orthonormal]

/-- The linear span of the logical frame. -/
def codeSpan {n K : ℕ} (F : OrthonormalFrame n K) :
    Submodule ℂ (SS.State n ℂ) :=
  Submodule.span ℂ (Set.range F.vec)

/-! ## Knill--Laflamme invariance under a logical change of basis -/

theorem innerC_add_left {n : ℕ} (phi chi eta : SS.State n ℂ) :
    SS.innerC (phi + chi) eta = SS.innerC phi eta + SS.innerC chi eta := by
  simp only [SS.innerC, Pi.add_apply, star_add, add_mul,
    Finset.sum_add_distrib]

theorem innerC_add_right {n : ℕ} (phi chi eta : SS.State n ℂ) :
    SS.innerC phi (chi + eta) = SS.innerC phi chi + SS.innerC phi eta := by
  simp only [SS.innerC, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem innerC_smul_left {n : ℕ} (a : ℂ) (phi chi : SS.State n ℂ) :
    SS.innerC (a • phi) chi = star a * SS.innerC phi chi := by
  simp only [SS.innerC, Pi.smul_apply, smul_eq_mul, star_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

@[simp] theorem innerC_zero_left {n : ℕ} (phi : SS.State n ℂ) :
    SS.innerC 0 phi = 0 := by
  simp [SS.innerC]

@[simp] theorem innerC_zero_right {n : ℕ} (phi : SS.State n ℂ) :
    SS.innerC phi 0 = 0 := by
  simp [SS.innerC]

theorem innerC_smul_right {n : ℕ} (a : ℂ) (phi chi : SS.State n ℂ) :
    SS.innerC phi (a • chi) = a * SS.innerC phi chi := by
  simp only [SS.innerC, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

@[simp] theorem pauliAct_zero {n : ℕ} (P : SS.PauliString n) :
    SS.pauliAct P (0 : SS.State n ℂ) = 0 := by
  funext x
  simp [SS.pauliAct, SS.signC]

theorem pauliAct_add {n : ℕ} (P : SS.PauliString n)
    (phi chi : SS.State n ℂ) :
    SS.pauliAct P (phi + chi) = SS.pauliAct P phi + SS.pauliAct P chi := by
  funext x
  by_cases h : SS.bdot P.z (SS.bxor x P.x) <;>
    simp [SS.pauliAct, SS.signC, h] <;> ring

theorem pauliAct_smul {n : ℕ} (P : SS.PauliString n) (a : ℂ)
    (phi : SS.State n ℂ) :
    SS.pauliAct P (a • phi) = a • SS.pauliAct P phi := by
  funext x
  by_cases h : SS.bdot P.z (SS.bxor x P.x) <;>
    simp [SS.pauliAct, SS.signC, h] <;> ring

/-- A KL matrix condition on one orthonormal frame is the scalar-compression
identity on its entire code span.  This is the basis-independent content of
Knill--Laflamme. -/
theorem scalarCompression_of_klCondition {n K : ℕ}
    (F : OrthonormalFrame n K) (P : SS.PauliString n)
    (hKL : SS.KLCondition F.vec P) :
    ∃ c : ℂ, ∀ phi, phi ∈ codeSpan F → ∀ chi, chi ∈ codeSpan F →
      SS.innerC phi (SS.pauliAct P chi) = c * SS.innerC phi chi := by
  rcases hKL with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  have hright (j : Fin K) : ∀ chi, chi ∈ codeSpan F →
      SS.innerC (F.vec j) (SS.pauliAct P chi) =
        c * SS.innerC (F.vec j) chi := by
    intro chi hchi
    refine Submodule.span_induction
      (p := fun chi _ => SS.innerC (F.vec j) (SS.pauliAct P chi) =
        c * SS.innerC (F.vec j) chi) ?_ ?_ ?_ ?_ hchi
    · rintro _ ⟨k, rfl⟩
      rw [hc j k, F.orthonormal]
      by_cases hjk : j = k <;> simp [hjk]
    · change SS.innerC (F.vec j) (SS.pauliAct P 0) =
        c * SS.innerC (F.vec j) 0
      rw [pauliAct_zero, innerC_zero_right]
      ring
    · intro x y _ _ hx hy
      rw [pauliAct_add, innerC_add_right, innerC_add_right, hx, hy]
      ring
    · intro a x _ hx
      rw [pauliAct_smul, innerC_smul_right, innerC_smul_right, hx]
      ring
  intro phi hphi
  refine Submodule.span_induction
    (p := fun phi _ => ∀ chi, chi ∈ codeSpan F →
      SS.innerC phi (SS.pauliAct P chi) = c * SS.innerC phi chi) ?_ ?_ ?_ ?_ hphi
  · rintro _ ⟨j, rfl⟩
    exact hright j
  · intro chi _
    rw [innerC_zero_left, innerC_zero_left]
    ring
  · intro x y _ _ hx hy chi hchi
    rw [innerC_add_left, innerC_add_left, hx chi hchi, hy chi hchi]
    ring
  · intro a x _ hx chi hchi
    rw [innerC_smul_left, innerC_smul_left, hx chi hchi]
    ring

/-- `HasDistance` is invariant under replacing an orthonormal logical frame by
any other orthonormal frame spanning the same code. -/
theorem hasDistance_of_codeSpan_eq {n K L d : ℕ}
    (F : OrthonormalFrame n K) (G : OrthonormalFrame n L)
    (hspan : codeSpan F = codeSpan G) (hF : SS.HasDistance F.vec d) :
    SS.HasDistance G.vec d := by
  intro P hP
  obtain ⟨c, hcompression⟩ := scalarCompression_of_klCondition F P (hF P hP)
  refine ⟨c, ?_⟩
  intro i j
  have hi : G.vec i ∈ codeSpan F := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have hj : G.vec j ∈ codeSpan F := by
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self j)
  rw [hcompression (G.vec i) hi (G.vec j) hj, G.orthonormal]
  by_cases hij : i = j <;> simp [hij]

/-- Projection always lands in the span of the logical frame. -/
theorem projectorAction_mem_codeSpan {n K : ℕ} (F : OrthonormalFrame n K)
    (phi : SS.State n ℂ) : projectorAction F phi ∈ codeSpan F := by
  classical
  have heq : projectorAction F phi =
      ∑ k, SS.innerC (F.vec k) phi • F.vec k := by
    funext x
    simp only [projectorAction, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  apply Submodule.sum_mem
  intro k _
  exact (codeSpan F).smul_mem (SS.innerC (F.vec k) phi)
    (Submodule.subset_span (Set.mem_range_self k))

@[simp] theorem projectorAction_zero {n K : ℕ} (F : OrthonormalFrame n K) :
    projectorAction F 0 = 0 := by
  funext x
  simp [projectorAction, SS.innerC]

theorem projectorAction_add {n K : ℕ} (F : OrthonormalFrame n K)
    (phi chi : SS.State n ℂ) :
    projectorAction F (phi + chi) =
      projectorAction F phi + projectorAction F chi := by
  funext x
  simp only [projectorAction, SS.innerC, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem projectorAction_smul {n K : ℕ} (F : OrthonormalFrame n K)
    (a : ℂ) (phi : SS.State n ℂ) :
    projectorAction F (a • phi) = a • projectorAction F phi := by
  funext x
  simp only [projectorAction, SS.innerC, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- A vector belongs to the code exactly when the frame projector fixes it. -/
theorem mem_codeSpan_iff_projectorAction_eq {n K : ℕ}
    (F : OrthonormalFrame n K) (phi : SS.State n ℂ) :
    phi ∈ codeSpan F ↔ projectorAction F phi = phi := by
  constructor
  · intro hphi
    refine Submodule.span_induction
      (p := fun phi _ => projectorAction F phi = phi) ?_ ?_ ?_ ?_ hphi
    · rintro _ ⟨k, rfl⟩
      exact projectorAction_vec F k
    · exact projectorAction_zero F
    · intro x y _ _ hx hy
      rw [projectorAction_add, hx, hy]
    · intro a x _ hx
      rw [projectorAction_smul, hx]
  · intro hfix
    rw [← hfix]
    exact projectorAction_mem_codeSpan F phi

/-- The frame projector is idempotent. -/
@[simp] theorem projectorAction_idempotent {n K : ℕ}
    (F : OrthonormalFrame n K) (phi : SS.State n ℂ) :
    projectorAction F (projectorAction F phi) = projectorAction F phi := by
  funext x
  simp only [projectorAction]
  exact Finset.sum_congr rfl fun k _ => by rw [innerC_projectorAction]

/-- The projector kernel is Hermitian, the coordinate form of self-adjointness. -/
theorem star_projectorKernel {n K : ℕ} (F : OrthonormalFrame n K)
    (x y : SS.BitString n) :
    star (projectorKernel F x y) = projectorKernel F y x := by
  classical
  simp [projectorKernel, mul_comm]

/-! ## Code-preserving operators and projective equality -/

/-- A linear operator preserves the code when it maps the frame span into
itself. -/
def CodePreserving {n K : ℕ} (F : OrthonormalFrame n K)
    (U : Module.End ℂ (SS.State n ℂ)) : Prop :=
  ∀ phi, phi ∈ codeSpan F → U phi ∈ codeSpan F

/-- It is enough, and necessary, to check preservation on the logical frame. -/
theorem codePreserving_iff_frame {n K : ℕ} (F : OrthonormalFrame n K)
    (U : Module.End ℂ (SS.State n ℂ)) :
    CodePreserving F U ↔ ∀ k, U (F.vec k) ∈ codeSpan F := by
  constructor
  · intro h k
    exact h _ (Submodule.subset_span (Set.mem_range_self k))
  · intro h phi hphi
    refine Submodule.span_induction (p := fun phi _ => U phi ∈ codeSpan F)
      ?_ ?_ ?_ ?_ hphi
    · rintro _ ⟨k, rfl⟩
      exact h k
    · simp
    · intro x y _ _ hx hy
      simpa using (codeSpan F).add_mem hx hy
    · intro a x _ hx
      simpa using (codeSpan F).smul_mem a hx

/-- Two linear operators induce the same projective action on a code if they
differ there by one nonzero scalar. -/
def SameProjectiveOnCode {n K : ℕ} (F : OrthonormalFrame n K)
    (U V : Module.End ℂ (SS.State n ℂ)) : Prop :=
  ∃ lam : ℂ, lam ≠ 0 ∧
    ∀ phi, phi ∈ codeSpan F → U phi = lam • V phi

/-- Faithful frame semantics for projective equality: because the operators
are linear, checking the ordered logical frame is equivalent to checking the
whole code span. -/
theorem sameProjectiveOnCode_iff_frame {n K : ℕ}
    (F : OrthonormalFrame n K) (U V : Module.End ℂ (SS.State n ℂ)) :
    SameProjectiveOnCode F U V ↔
      ∃ lam : ℂ, lam ≠ 0 ∧ ∀ k, U (F.vec k) = lam • V (F.vec k) := by
  constructor
  · rintro ⟨lam, hlam, h⟩
    exact ⟨lam, hlam, fun k => h _ (Submodule.subset_span (Set.mem_range_self k))⟩
  · rintro ⟨lam, hlam, hframe⟩
    refine ⟨lam, hlam, fun phi hphi => ?_⟩
    refine Submodule.span_induction
      (p := fun phi _ => U phi = lam • V phi) ?_ ?_ ?_ ?_ hphi
    · rintro _ ⟨k, rfl⟩
      exact hframe k
    · simp
    · intro x y _ _ hx hy
      simp [map_add, hx, hy, smul_add]
    · intro a x _ hx
      simp [map_smul, hx, smul_smul, mul_comm]

/-! ## Paper-normalized Shor--Laflamme enumerators -/

/-- The normalized coefficient of `main.tex`:
`A_w = K^{-2} ∑_{wt(E)=w} |Tr(EP)|²`.

The arithmetic expression is total as a Lean function.  Paper-facing uses are
through `ExactCode`, whose `positiveRank` field rules out `K = 0`. -/
def AWeight {n K : ℕ} (F : OrthonormalFrame n K) (w : ℕ) : ℝ :=
  SS.MacWilliams.Aco F.vec w / (K : ℝ) ^ 2

/-- The paper-normalized Frobenius coefficient
`B_w = K^{-2} Bco_w` in the repository's historical convention. -/
def BWeight {n K : ℕ} (F : OrthonormalFrame n K) (w : ℕ) : ℝ :=
  SS.MacWilliams.Bco F.vec w / (K : ℝ) ^ 2

/-- For one logical qubit (`K = 2`), the historical `Aco` convention is four
times the paper's normalized coefficient. -/
theorem Aco_eq_four_mul_AWeight {n : ℕ} (F : OrthonormalFrame n 2) (w : ℕ) :
    SS.MacWilliams.Aco F.vec w = 4 * AWeight F w := by
  norm_num [AWeight]
  ring

/-- The same factor-four conversion for the `B` enumerator at `K = 2`. -/
theorem Bco_eq_four_mul_BWeight {n : ℕ} (F : OrthonormalFrame n 2) (w : ℕ) :
    SS.MacWilliams.Bco F.vec w = 4 * BWeight F w := by
  norm_num [BWeight]
  ring

/-- Auxiliary image of a *supplied* restriction on exact codes.

This is intentionally not named `WImage`: an arbitrary predicate (notably
`False`) does not define one of the paper's orbit images.  A paper-facing
`WImage r` must instantiate and justify a concrete orbit-membership predicate. -/
def RestrictedAImage {n K d : ℕ} (admissible : ExactCode n K d → Prop) :
    Set (Fin (n + 1) → ℝ) :=
  { A | ∃ C : ExactCode n K d, admissible C ∧
      ∀ w : Fin (n + 1), A w = AWeight C.frame w }

end

end MainTheory.CodeSpec
