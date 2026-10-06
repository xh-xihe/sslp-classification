import SixQubit.Orbit8UniversalSupport
import SixQubit.Orbit8RaisingGramAlgebra

/-!
# The raising-Gram corollary for arbitrary orbit-8 codes

The matrix is the Gram matrix of the six actual singly raised logical-zero
vectors.  Full-fiber containment permits all boundary supports.  Its
characteristic polynomial records the multiplicities in the manuscript.
-/

namespace SixQubit.Orbit8RaisingGram

open SixQubit.Orbit8Universal
open SS.MacWilliams
open scoped BigOperators ComplexConjugate Matrix

noncomputable section

def singleRaise (i : Fin 6) (f : SS.State 6 ℂ) : SS.State 6 ℂ :=
  fun x => if x i = true then f (SS.bxor x (SS.stdBasis i)) else 0

def singleLower (i : Fin 6) (f : SS.State 6 ℂ) : SS.State 6 ℂ :=
  fun x => if x i = false then f (SS.bxor x (SS.stdBasis i)) else 0

/-- The physical raising-vector Gram matrix `G_+`. -/
def raisingGram (c : SS.State 6 ℂ) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => SS.innerC (singleRaise i c) (singleRaise j c)

theorem singleRaise_adjoint (i : Fin 6) (f g : SS.State 6 ℂ) :
    SS.innerC (singleRaise i f) g = SS.innerC f (singleLower i g) := by
  classical
  unfold SS.innerC
  calc
    _ = ∑ x, star (singleRaise i f (SS.bxor x (SS.stdBasis i))) *
        g (SS.bxor x (SS.stdBasis i)) :=
      (Equiv.sum_comp (SS.bxorEquiv (SS.stdBasis i))
        (fun x => star (singleRaise i f x) * g x)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      have hcancel : SS.bxor (SS.stdBasis i) (SS.bxor x (SS.stdBasis i)) = x := by
        rw [SS.bxor_comm (SS.stdBasis i), SS.bxor_bxor_cancel]
      cases hxi : x i <;>
        simp [singleRaise, singleLower, hxi, hcancel]

theorem lowering_raising_self (i : Fin 6) (f : SS.State 6 ℂ) :
    singleLower i (singleRaise i f) = fun x => f x - projOne i f x := by
  funext x
  have hcancel : SS.bxor (SS.stdBasis i) (SS.bxor x (SS.stdBasis i)) = x := by
    rw [SS.bxor_comm (SS.stdBasis i), SS.bxor_bxor_cancel]
  cases hxi : x i <;>
    simp [singleLower, singleRaise, projOne, hxi, hcancel]

theorem lowering_raising_ne (i j : Fin 6) (hij : i ≠ j) (f : SS.State 6 ℂ) :
    singleLower i (singleRaise j f) = hop j i f := by
  funext x
  have hbit : SS.stdBasis i j = false := SS.stdBasis_apply_ne (Ne.symm hij)
  have hswap : SS.bxor (SS.bxor x (SS.stdBasis i)) (SS.stdBasis j) =
      SS.bxor x (pairMask j i) := by
    rw [SS.bxor_assoc, ← pairMask, pairMask_swap]
  cases hxi : x i <;> cases hxj : x j <;>
    simp [singleLower, singleRaise, hop, hbit, hxi, hxj, hswap]

private theorem qA_swap (ud : Fin 6 → ℂ) (i j : Fin 6) :
    qA ud (j,i) = qA ud (i,j) := by
  simp [qA, zpair, star_mul']
  ring

private theorem qB_swap (ud : Fin 6 → ℂ) (i j : Fin 6) :
    qB ud (j,i) = -qB ud (i,j) := by
  simp [qB, zpair, star_mul']
  ring

section Code

variable (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hcode

private theorem pair_traces_ordered (i j : Fin 6) (hij : i < j) :
    trProj ![c,d] (Pxx i j) = 24 * qA (u d) (i,j) ∧
    trProj ![c,d] (Pxy i j) = 24 * qB (u d) (i,j) ∧
    trProj ![c,d] (Pyx i j) = -24 * qB (u d) (i,j) ∧
    trProj ![c,d] (Pyy i j) = 24 * qA (u d) (i,j) := by
  let ij : Pair6 := ⟨(i,j), by simp [pairs6, hij]⟩
  have h0 := trace_saturation c d hc hd hnc hnd hcode (Sum.inr (ij,0))
  have h1 := trace_saturation c d hc hd hnc hnd hcode (Sum.inr (ij,1))
  have h2 := trace_saturation c d hc hd hnc hnd hcode (Sum.inr (ij,2))
  have h3 := trace_saturation c d hc hd hnc hnd hcode (Sum.inr (ij,3))
  change trProj ![c,d] (Pxx i j) = 24 * qA (u d) (i,j) at h0
  change trProj ![c,d] (Pxy i j) = 24 * qB (u d) (i,j) at h1
  change trProj ![c,d] (Pyx i j) = 24 * -qB (u d) (i,j) at h2
  change trProj ![c,d] (Pyy i j) = 24 * qA (u d) (i,j) at h3
  exact ⟨h0,h1,by linear_combination h2,h3⟩

private theorem pair_traces (i j : Fin 6) (hij : i ≠ j) :
    trProj ![c,d] (Pxx i j) = 24 * qA (u d) (i,j) ∧
    trProj ![c,d] (Pxy i j) = 24 * qB (u d) (i,j) ∧
    trProj ![c,d] (Pyx i j) = -24 * qB (u d) (i,j) ∧
    trProj ![c,d] (Pyy i j) = 24 * qA (u d) (i,j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact pair_traces_ordered c d hc hd hnc hnd hcode i j hlt
  · obtain ⟨h0,h1,h2,h3⟩ := pair_traces_ordered c d hc hd hnc hnd hcode j i hgt
    rw [Pxx_swap, qA_swap] at h0
    rw [Pxy_swap, qB_swap] at h1
    rw [Pyx_swap, qB_swap] at h2
    rw [Pyy_swap, qA_swap] at h3
    exact ⟨h0, by linear_combination h2, by linear_combination h1, h3⟩

omit hc hd hnc hnd in
private theorem c_expect_half_trace (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    SS.innerC c (SS.pauliAct P c) = trProj ![c,d] P / 2 :=
  (expect_eq_of_hasDistance c d hcode P hw).trans
    (expect_half_trace c d hcode P hw)

theorem inner_hop_saturated (i j : Fin 6) (hij : i ≠ j) :
    SS.innerC c (hop i j c) = 3 * star (u d i) * u d j := by
  obtain ⟨h0,h1,h2,h3⟩ := pair_traces c d hc hd hnc hnd hcode i j hij
  rw [inner_hop c i j hij,
    c_expect_half_trace c d hcode (Pxx i j) (wt_Pxx i j),
    c_expect_half_trace c d hcode (Pxy i j) (wt_Pxy i j),
    c_expect_half_trace c d hcode (Pyx i j) (wt_Pyx i j),
    c_expect_half_trace c d hcode (Pyy i j) (wt_Pyy i j), h0,h1,h2,h3]
  simp only [qA, qB, zpair, star_mul', star_star]
  ring_nf
  simp [Complex.I_sq]
  ring

theorem inner_z_saturated (i : Fin 6) :
    SS.innerC c (SS.pauliAct (Pz i) c) = -6 * (p d i : ℂ) := by
  have ht := trace_saturation c d hc hd hnc hnd hcode (Sum.inl i)
  change trProj ![c,d] (Pz i) = 24 * (-((p d i : ℂ) / 2)) at ht
  rw [c_expect_half_trace c d hcode (Pz i) (wt_Pz i), ht]
  ring

/-- The actual raising Gram matrix is the matrix forced by saturation of
the low-weight Pauli coefficients. -/
theorem raisingGram_eq_normalMatrix : raisingGram c = normalMatrix (u d) := by
  ext i j
  rw [raisingGram, singleRaise_adjoint]
  by_cases hij : i = j
  · subst j
    rw [lowering_raising_self]
    have he : SS.innerC c (fun x => c x - projOne i c x) =
        SS.innerC c c - SS.innerC c (projOne i c) := by
      simp only [SS.innerC, mul_sub, Finset.sum_sub_distrib]
    rw [he, inner_projOne, hnc, inner_z_saturated c d hc hd hnc hnd hcode i]
    simp only [normalMatrix, ↓reduceIte, p]
    have hn : star (u d i) * u d i = (Complex.normSq (u d i) : ℂ) :=
      Complex.normSq_eq_conj_mul_self.symm
    linear_combination (-3 : ℂ) * hn
  · rw [lowering_raising_ne i j hij,
      inner_hop_saturated c d hc hd hnc hnd hcode j i (Ne.symm hij)]
    simp only [normalMatrix, if_neg hij, zero_add]
    ring

/-- The corollary's idempotence and complete eigenvalue multiplicities,
directly for an arbitrary code supported in the two full orbit-8 fibers. -/
theorem fully_certified :
    raisingGram c * raisingGram c = (1/2 : ℂ) • raisingGram c ∧
      (raisingGram c).charpoly =
        Polynomial.X * (Polynomial.X - Polynomial.C (1/2 : ℂ)) ^ 5 := by
  rw [raisingGram_eq_normalMatrix c d hc hd hnc hnd hcode]
  apply normalMatrix_square_and_charpoly
  · exact (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  · have hs := singleton_support_le_two c d hc hd hnc hnd hcode
    simpa [probabilitySupport, p, Complex.normSq_eq_zero] using hs

end Code

end

end SixQubit.Orbit8RaisingGram
