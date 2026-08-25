import SixQubit.Orbit8UniversalLow
import SixQubit.Pin

/-!
# Orbit 8 universal converse, VIII: equality in the low sector

The shadow inequality turns the preceding lower bound into equality.  This
file then proves the equality case of the finite Cauchy--Schwarz argument
inside Lean and obtains every individual low-weight trace coefficient.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit
open SS.MacWilliams

set_option maxRecDepth 20000

noncomputable section

lemma normalized_pair (c d : SS.BitString 6 → ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1) :
    ∀ k : Fin 2, SS.innerC (![c,d] k) (![c,d] k) = 1 := by
  intro k
  fin_cases k
  · exact hnc
  · exact hnd

/-- The complete raw `A` line except for the still-free split between weights
one and two. -/
theorem universal_pin_line (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    Aco ![c,d] 1 + Aco ![c,d] 2 = 4 ∧ Aco ![c,d] 3 = 0
      ∧ Aco ![c,d] 4 = 44 + 4 * Aco ![c,d] 1
      ∧ Aco ![c,d] 5 = 64 - Aco ![c,d] 1
      ∧ Aco ![c,d] 6 = 12 - 3 * Aco ![c,d] 1 := by
  have hA0 := SixQubit.Pin.Aco_zero ![c,d] (normalized_pair c d hnc hnd)
  exact SixQubit.Pin.pin_line ![c,d] hcode hA0
    (low_bound c d hc hd hnc hnd hcode)

lemma qCoeff_star (ud : Fin 6 → ℂ) (e : QIndex) :
    star (qCoeff ud e) = qCoeff ud e := by
  rcases e with i | ⟨ij,t⟩
  · simp [qCoeff]
  · fin_cases t <;>
      simp [qCoeff, qA, qB, star_add, star_sub, star_mul'] <;>
      ring

theorem indexed_trace_norm (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    (∑ e : QIndex, Complex.normSq (trProj ![c,d] (qPauli e))) = 4 := by
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  have hmass : (∑ i, Complex.normSq (u d i)) = (1/6 : ℝ) := by
    simpa [r, p] using hr
  have hqn : (∑ e : QIndex, Complex.normSq (qCoeff (u d) e)) = (1/144 : ℝ) := by
    rw [qCoeff_norm, hmass]
    norm_num
  have hdot := q_dot_trace c d hc hd hnc hnd hcode
  have hcs := finite_complex_cauchy (qCoeff (u d))
    (fun e : QIndex => trProj ![c,d] (qPauli e))
  rw [hdot, hqn] at hcs
  norm_num [Complex.normSq_div, Complex.normSq_ofReal] at hcs
  have hle := q_trace_norm_le_A12 ![c,d]
  have hsum := (universal_pin_line c d hc hd hnc hnd hcode).1
  rw [Fintype.sum_sum_type] at hle
  rw [Fintype.sum_sum_type]
  nlinarith

/-- Equality in the low-sector Cauchy--Schwarz inequality, coefficient by
coefficient.  The factor `24` is in raw projector-trace convention. -/
theorem trace_saturation (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∀ e : QIndex,
      trProj ![c,d] (qPauli e) = 24 * qCoeff (u d) e := by
  let xq : EuclideanSpace ℂ QIndex :=
    WithLp.toLp 2 (fun e => star (qCoeff (u d) e))
  let xt : EuclideanSpace ℂ QIndex :=
    WithLp.toLp 2 (fun e => trProj ![c,d] (qPauli e))
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  have hmass : (∑ i, Complex.normSq (u d i)) = (1/6 : ℝ) := by
    simpa [r, p] using hr
  have hqn : (∑ e : QIndex, Complex.normSq (qCoeff (u d) e)) = (1/144 : ℝ) := by
    rw [qCoeff_norm, hmass]
    norm_num
  have ht := indexed_trace_norm c d hc hd hnc hnd hcode
  have hxq2 : ‖xq‖ ^ 2 = (1/144 : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [xq, norm_star, Complex.sq_norm]
    exact hqn
  have hxt2 : ‖xt‖ ^ 2 = (4 : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [xt, Complex.sq_norm]
    exact ht
  have hxq : ‖xq‖ = (1/12 : ℝ) := by
    have hn := norm_nonneg xq
    nlinarith
  have hxt : ‖xt‖ = (2 : ℝ) := by
    have hn := norm_nonneg xt
    nlinarith
  have hinner : inner ℂ xq xt = (1/6 : ℂ) := by
    rw [PiLp.inner_apply]
    simp only [xq, xt, RCLike.inner_apply, starRingEnd_apply, star_star]
    rw [Finset.sum_congr rfl (fun e he => by rw [mul_comm])]
    exact q_dot_trace c d hc hd hnc hnd hcode
  have heq : inner ℂ xq xt = ((‖xq‖ : ℂ) * (‖xt‖ : ℂ)) := by
    rw [hinner, hxq, hxt]
    norm_num
  have hparallel := (inner_eq_norm_mul_iff (x := xq) (y := xt)).mp heq
  intro e
  have he := congrArg (fun z : EuclideanSpace ℂ QIndex => z e) hparallel
  change ((‖xt‖ : ℂ) * star (qCoeff (u d) e)) =
    (‖xq‖ : ℂ) * trProj ![c,d] (qPauli e) at he
  rw [hxt, hxq, qCoeff_star] at he
  norm_num at he
  calc
    trProj ![c,d] (qPauli e) =
        12 * ((1/12 : ℂ) * trProj ![c,d] (qPauli e)) := by ring
    _ = 12 * (2 * qCoeff (u d) e) := by rw [← he]
    _ = 24 * qCoeff (u d) e := by ring

theorem trace_zero_low_outside (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (P : SS.PauliString 6) (hP : P ∈ lowPaulis)
    (hout : P ∉ Finset.univ.image qPauli) :
    trProj ![c,d] P = 0 := by
  let F := fun P : SS.PauliString 6 => Complex.normSq (trProj ![c,d] P)
  have himg : (∑ P ∈ Finset.univ.image qPauli, F P) = 4 := by
    rw [Finset.sum_image qPauli_injective.injOn]
    exact indexed_trace_norm c d hc hd hnc hnd hcode
  have hlow : (∑ P ∈ lowPaulis, F P) = 4 := by
    rw [lowPaulis_sum]
    exact (universal_pin_line c d hc hd hnc hnd hcode).1
  have hsplit := Finset.sum_sdiff (f := F) qPauli_image_subset
  have hzero : (∑ P ∈ lowPaulis \ Finset.univ.image qPauli, F P) = 0 := by
    linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun Q hQ => Complex.normSq_nonneg (trProj ![c,d] Q))).mp hzero
  have hFP := hall P (by simp [hP, hout])
  exact Complex.normSq_eq_zero.mp hFP

theorem wt_Pz_exact : ∀ i : Fin 6, (Pz i).wt = 1 := by decide

theorem qPauli_weight_one_image : ∀ e : QIndex, (qPauli e).wt = 1 →
    ∃ i : Fin 6, qPauli e = Pz i := by decide

/-- The free line parameter is the concentration of the singleton shell:
`Aco₁ = 144 Σ pᵢ²` in raw convention. -/
theorem Aco_one_p (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    Aco ![c,d] 1 = 144 * ∑ i, (p d i) ^ 2 := by
  let W1 := Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 1)
  let Zs : Finset (SS.PauliString 6) := Finset.univ.image Pz
  have hzsub : Zs ⊆ W1 := by
    intro P hP
    rw [Finset.mem_image] at hP
    obtain ⟨i, hi, rfl⟩ := hP
    simp [W1, wt_Pz_exact]
  have hout : ∀ P ∈ W1, P ∉ Zs → trProj ![c,d] P = 0 := by
    intro P hPW hPZ
    have hwt : P.wt = 1 := by simpa [W1] using hPW
    apply trace_zero_low_outside c d hc hd hnc hnd hcode P
    · simp [lowPaulis, hwt]
    · intro himg
      rw [Finset.mem_image] at himg
      obtain ⟨e, he, hPe⟩ := himg
      have hewt : (qPauli e).wt = 1 := by rwa [hPe]
      obtain ⟨i, hi⟩ := qPauli_weight_one_image e hewt
      apply hPZ
      rw [Finset.mem_image]
      exact ⟨i, Finset.mem_univ _, hi.symm.trans hPe⟩
  have hsum := Finset.sum_subset
    (f := fun P => Complex.normSq (trProj ![c,d] P)) hzsub (fun P hPW hPZ => by
    change Complex.normSq (trProj ![c,d] P) = 0
    rw [hout P hPW hPZ, Complex.normSq_zero])
  change (∑ P ∈ Zs, Complex.normSq (trProj ![c,d] P)) =
    (∑ P ∈ W1, Complex.normSq (trProj ![c,d] P)) at hsum
  rw [Aco]
  change (∑ P ∈ W1, Complex.normSq (trProj ![c,d] P)) = _
  rw [← hsum]
  dsimp only [Zs]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have ht := trace_saturation c d hc hd hnc hnd hcode (Sum.inl i)
    simp only [qPauli, qCoeff] at ht
    rw [ht, Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_div,
      Complex.normSq_ofReal]
    unfold p
    norm_num
    ring
  · intro i hi j hj hij
    exact stdBasis_injective (congrArg SS.PauliString.z hij)

end

end SixQubit.Orbit8Universal
