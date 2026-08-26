import SixQubit.Orbit8UniversalLadderClose

/-!
# Orbit 8 universal converse, VII: low-weight saturation

This file expands `Q` in an injectively indexed set of one- and two-qubit
Paulis, proves the exact squared norm of its nonidentity coefficient vector,
and applies finite Cauchy--Schwarz to obtain the raw bound
`4 ≤ Aco₁ + Aco₂`.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit
open SS.MacWilliams

set_option maxRecDepth 20000

noncomputable section

def pairs6 : Finset (Fin 6 × Fin 6) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

theorem pairs6_eq : pairs6 =
    ({(0,1),(0,2),(0,3),(0,4),(0,5),
      (1,2),(1,3),(1,4),(1,5),
      (2,3),(2,4),(2,5),(3,4),(3,5),(4,5)} : Finset (Fin 6 × Fin 6)) := by decide

theorem sum_ordered_decompose (F : Fin 6 → Fin 6 → ℂ) :
    (∑ i, ∑ j, F i j) =
      (∑ i, F i i) + ∑ ij ∈ pairs6, (F ij.1 ij.2 + F ij.2 ij.1) := by
  rw [pairs6_eq]
  simp [Fin.sum_univ_succ]
  ring

def zpair (ud : Fin 6 → ℂ) (ij : Fin 6 × Fin 6) : ℂ :=
  ud ij.1 * star (ud ij.2)

def qA (ud : Fin 6 → ℂ) (ij : Fin 6 × Fin 6) : ℂ :=
  (zpair ud ij + star (zpair ud ij)) / 4

def qB (ud : Fin 6 → ℂ) (ij : Fin 6 × Fin 6) : ℂ :=
  Complex.I * (zpair ud ij - star (zpair ud ij)) / 4

lemma pairMask_swap (i j : Fin 6) : pairMask j i = pairMask i j := by
  unfold pairMask
  rw [SS.bxor_comm]

lemma Pxx_swap (i j : Fin 6) : Pxx j i = Pxx i j := by
  unfold Pxx
  rw [pairMask_swap]

lemma Pyy_swap (i j : Fin 6) : Pyy j i = Pyy i j := by
  unfold Pyy
  rw [pairMask_swap]

lemma Pxy_swap (i j : Fin 6) : Pxy j i = Pyx i j := by
  unfold Pxy Pyx
  rw [pairMask_swap]

lemma Pyx_swap (i j : Fin 6) : Pyx j i = Pxy i j := by
  unfold Pxy Pyx
  rw [pairMask_swap]

lemma pair_group (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ)
    (i j : Fin 6) (hij : i ≠ j) :
    (fun x => ud i * star (ud j) * rl i j f x
      + ud j * star (ud i) * rl j i f x) =
    fun x =>
      qA ud (i,j) * SS.pauliAct (Pxx i j) f x
      + qB ud (i,j) * SS.pauliAct (Pxy i j) f x
      - qB ud (i,j) * SS.pauliAct (Pyx i j) f x
      + qA ud (i,j) * SS.pauliAct (Pyy i j) f x := by
  rw [rl_ne i j hij, rl_ne j i (Ne.symm hij)]
  rw [hop_pauli i j hij, hop_pauli j i (Ne.symm hij)]
  funext x
  rw [Pxx_swap i j, Pyy_swap i j, Pxy_swap i j, Pyx_swap i j]
  unfold qA qB zpair
  simp only [star_mul', star_star]
  ring

lemma diag_group (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) (i : Fin 6) :
    (fun x => ud i * star (ud i) * rl i i f x) =
      fun x => ((Complex.normSq (ud i) : ℂ) / 2) * f x
        - ((Complex.normSq (ud i) : ℂ) / 2) * SS.pauliAct (Pz i) f x := by
  rw [rl_self, projOne_pauli]
  funext x
  push_cast [← SixQubit.star_mul_self]
  ring

/-- The exact Pauli expansion of `Q`. -/
theorem Q_pauli_expand (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) :
    Qact ud f = fun x =>
      (((∑ i, Complex.normSq (ud i) : ℝ) : ℂ) / 2) * f x
      + ∑ i, (-((Complex.normSq (ud i) : ℂ) / 2)) * SS.pauliAct (Pz i) f x
      + ∑ ij ∈ pairs6,
          (qA ud ij * SS.pauliAct (Pxx ij.1 ij.2) f x
          + qB ud ij * SS.pauliAct (Pxy ij.1 ij.2) f x
          - qB ud ij * SS.pauliAct (Pyx ij.1 ij.2) f x
          + qA ud ij * SS.pauliAct (Pyy ij.1 ij.2) f x) := by
  rw [Qact_expand]
  funext x
  rw [sum_ordered_decompose]
  calc
    (∑ i, ud i * star (ud i) * rl i i f x) +
        ∑ ij ∈ pairs6,
          (ud ij.1 * star (ud ij.2) * rl ij.1 ij.2 f x
            + ud ij.2 * star (ud ij.1) * rl ij.2 ij.1 f x) =
      (∑ i, (((Complex.normSq (ud i) : ℂ) / 2) * f x
        - ((Complex.normSq (ud i) : ℂ) / 2) * SS.pauliAct (Pz i) f x)) +
        ∑ ij ∈ pairs6,
          (ud ij.1 * star (ud ij.2) * rl ij.1 ij.2 f x
            + ud ij.2 * star (ud ij.1) * rl ij.2 ij.1 f x) := by
      congr 1
      exact Finset.sum_congr rfl (fun i hi => congrFun (diag_group ud f i) x)
    _ = (∑ i, (((Complex.normSq (ud i) : ℂ) / 2) * f x
        - ((Complex.normSq (ud i) : ℂ) / 2) * SS.pauliAct (Pz i) f x)) +
        ∑ ij ∈ pairs6,
          (qA ud ij * SS.pauliAct (Pxx ij.1 ij.2) f x
          + qB ud ij * SS.pauliAct (Pxy ij.1 ij.2) f x
          - qB ud ij * SS.pauliAct (Pyx ij.1 ij.2) f x
          + qA ud ij * SS.pauliAct (Pyy ij.1 ij.2) f x) := by
      congr 1
      exact Finset.sum_congr rfl (fun ij hij => by
        have hlt := (Finset.mem_filter.mp hij).2
        exact congrFun (pair_group ud f ij.1 ij.2 (ne_of_lt hlt)) x)
    _ = _ := by
      push_cast
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have hcoeff : (∑ i, ((Complex.normSq (ud i) : ℂ) / 2) * f x) =
          ((∑ i, (Complex.normSq (ud i) : ℂ)) / 2) * f x := by
        simp_rw [div_eq_mul_inv]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      rw [hcoeff]
      have hz : -(∑ i, ((Complex.normSq (ud i) : ℂ) / 2) *
          SS.pauliAct (Pz i) f x) =
          ∑ i, (-((Complex.normSq (ud i) : ℂ) / 2)) *
            SS.pauliAct (Pz i) f x := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i hi => by ring)
      rw [sub_eq_add_neg, hz]

/-! ### An injective finite index for the 66 nonidentity low-weight Paulis -/

abbrev Pair6 := {ij : Fin 6 × Fin 6 // ij ∈ pairs6}

abbrev QIndex := Fin 6 ⊕ (Pair6 × Fin 4)

def qPauli : QIndex → SS.PauliString 6
  | .inl i => Pz i
  | .inr (ij, 0) => Pxx ij.1.1 ij.1.2
  | .inr (ij, 1) => Pxy ij.1.1 ij.1.2
  | .inr (ij, 2) => Pyx ij.1.1 ij.1.2
  | .inr (ij, 3) => Pyy ij.1.1 ij.1.2

def qCoeff (ud : Fin 6 → ℂ) : QIndex → ℂ
  | .inl i => -((Complex.normSq (ud i) : ℂ) / 2)
  | .inr (ij, 0) => qA ud ij.1
  | .inr (ij, 1) => qB ud ij.1
  | .inr (ij, 2) => -qB ud ij.1
  | .inr (ij, 3) => qA ud ij.1

theorem qPauli_injective : Function.Injective qPauli := by decide

theorem qPauli_weight : ∀ a : QIndex, (qPauli a).wt = 1 ∨ (qPauli a).wt = 2 := by
  decide

lemma qAB_norm (z : ℂ) :
    2 * Complex.normSq ((z + star z) / 4) +
      2 * Complex.normSq (Complex.I * (z - star z) / 4) =
        Complex.normSq z / 2 := by
  norm_num [Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.mul_re, Complex.mul_im]
  ring

lemma normSq_zpair (ud : Fin 6 → ℂ) (ij : Fin 6 × Fin 6) :
    Complex.normSq (zpair ud ij) =
      Complex.normSq (ud ij.1) * Complex.normSq (ud ij.2) := by
  simp [zpair, Complex.normSq_mul]

lemma qpair_norm (ud : Fin 6 → ℂ) (ij : Fin 6 × Fin 6) :
    Complex.normSq (qA ud ij) + Complex.normSq (qB ud ij) +
        Complex.normSq (-qB ud ij) + Complex.normSq (qA ud ij) =
      Complex.normSq (ud ij.1) * Complex.normSq (ud ij.2) / 2 := by
  rw [Complex.normSq_neg]
  have h := qAB_norm (zpair ud ij)
  unfold qA qB
  rw [normSq_zpair] at h
  linarith

lemma qCoeff_norm_expand (ud : Fin 6 → ℂ) :
    (∑ a : QIndex, Complex.normSq (qCoeff ud a)) =
      (∑ i : Fin 6, Complex.normSq (-((Complex.normSq (ud i) : ℂ) / 2))) +
      ∑ ij : Pair6,
        (Complex.normSq (qA ud ij.1) + Complex.normSq (qB ud ij.1) +
          Complex.normSq (-qB ud ij.1) + Complex.normSq (qA ud ij.1)) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [qCoeff, Fin.sum_univ_succ, add_assoc]

lemma pair_mass_identity (p : Fin 6 → ℝ) :
    (∑ i, p i * p i / 4) + ∑ ij ∈ pairs6, p ij.1 * p ij.2 / 2 =
      (∑ i, p i) ^ 2 / 4 := by
  rw [pairs6_eq]
  simp [Fin.sum_univ_succ]
  ring

lemma qCoeff_norm (ud : Fin 6 → ℂ) :
    (∑ a : QIndex, Complex.normSq (qCoeff ud a)) =
      (∑ i, Complex.normSq (ud i)) ^ 2 / 4 := by
  rw [qCoeff_norm_expand]
  have hz : (∑ i : Fin 6,
      Complex.normSq (-((Complex.normSq (ud i) : ℂ) / 2))) =
      ∑ i, Complex.normSq (ud i) * Complex.normSq (ud i) / 4 := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Complex.normSq_neg, Complex.normSq_div, Complex.normSq_ofReal]
    norm_num
  rw [hz]
  have hp : (∑ ij : Pair6,
      (Complex.normSq (qA ud ij.1) + Complex.normSq (qB ud ij.1) +
        Complex.normSq (-qB ud ij.1) + Complex.normSq (qA ud ij.1))) =
      ∑ ij ∈ pairs6,
        Complex.normSq (ud ij.1) * Complex.normSq (ud ij.2) / 2 := by
    change (∑ ij ∈ pairs6.attach,
      (Complex.normSq (qA ud ij.1) + Complex.normSq (qB ud ij.1) +
        Complex.normSq (-qB ud ij.1) + Complex.normSq (qA ud ij.1))) = _
    calc
      _ = ∑ ij ∈ pairs6.attach,
          Complex.normSq (ud ij.1.1) * Complex.normSq (ud ij.1.2) / 2 := by
        exact Finset.sum_congr rfl (fun ij hij => qpair_norm ud ij.1)
      _ = _ := by
        simpa using Finset.sum_attach pairs6
          (fun ij => Complex.normSq (ud ij.1) * Complex.normSq (ud ij.2) / 2)
  rw [hp]
  exact pair_mass_identity (fun i => Complex.normSq (ud i))

lemma qPauli_sum_expand (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ)
    (x : SS.BitString 6) :
    (∑ a : QIndex, qCoeff ud a * SS.pauliAct (qPauli a) f x) =
      (∑ i, (-((Complex.normSq (ud i) : ℂ) / 2)) *
          SS.pauliAct (Pz i) f x) +
      ∑ ij ∈ pairs6,
        (qA ud ij * SS.pauliAct (Pxx ij.1 ij.2) f x
          + qB ud ij * SS.pauliAct (Pxy ij.1 ij.2) f x
          - qB ud ij * SS.pauliAct (Pyx ij.1 ij.2) f x
          + qA ud ij * SS.pauliAct (Pyy ij.1 ij.2) f x) := by
  rw [Fintype.sum_sum_type]
  change (∑ i : Fin 6, (-((Complex.normSq (ud i) : ℂ) / 2)) *
      SS.pauliAct (Pz i) f x) +
      (∑ it : Pair6 × Fin 4,
        qCoeff ud (.inr it) * SS.pauliAct (qPauli (.inr it)) f x) = _
  congr 1
  rw [Fintype.sum_prod_type]
  have htag : ∀ ij : Pair6,
      (∑ t : Fin 4,
        qCoeff ud (.inr (ij,t)) * SS.pauliAct (qPauli (.inr (ij,t))) f x) =
        (qA ud ij.1 * SS.pauliAct (Pxx ij.1.1 ij.1.2) f x
          + qB ud ij.1 * SS.pauliAct (Pxy ij.1.1 ij.1.2) f x
          - qB ud ij.1 * SS.pauliAct (Pyx ij.1.1 ij.1.2) f x
          + qA ud ij.1 * SS.pauliAct (Pyy ij.1.1 ij.1.2) f x) := by
    intro ij
    rw [show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} by decide]
    simp [qCoeff, qPauli]
    ring
  rw [Finset.sum_congr rfl (fun ij hij => htag ij)]
  change (∑ ij ∈ pairs6.attach,
    (qA ud ij.1 * SS.pauliAct (Pxx ij.1.1 ij.1.2) f x
      + qB ud ij.1 * SS.pauliAct (Pxy ij.1.1 ij.1.2) f x
      - qB ud ij.1 * SS.pauliAct (Pyx ij.1.1 ij.1.2) f x
      + qA ud ij.1 * SS.pauliAct (Pyy ij.1.1 ij.1.2) f x)) = _
  simpa using Finset.sum_attach pairs6 (fun ij =>
    qA ud ij * SS.pauliAct (Pxx ij.1 ij.2) f x
      + qB ud ij * SS.pauliAct (Pxy ij.1 ij.2) f x
      - qB ud ij * SS.pauliAct (Pyx ij.1 ij.2) f x
      + qA ud ij * SS.pauliAct (Pyy ij.1 ij.2) f x)

/-- The low-weight part of `Q` indexed without repetition. -/
theorem Q_pauli_indexed (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) :
    Qact ud f = fun x =>
      (((∑ i, Complex.normSq (ud i) : ℝ) : ℂ) / 2) * f x +
        ∑ a : QIndex, qCoeff ud a * SS.pauliAct (qPauli a) f x := by
  rw [Q_pauli_expand]
  funext x
  rw [qPauli_sum_expand]
  ring

lemma inner_Q_pauli_indexed (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) :
    SS.innerC f (Qact ud f) =
      (((∑ i, Complex.normSq (ud i) : ℝ) : ℂ) / 2) * SS.innerC f f +
        ∑ a : QIndex,
          qCoeff ud a * SS.innerC f (SS.pauliAct (qPauli a) f) := by
  rw [Q_pauli_indexed]
  unfold SS.innerC
  change (∑ x, star (f x) *
      (((((∑ i, Complex.normSq (ud i) : ℝ) : ℂ) / 2) * f x) +
        ∑ a : QIndex, qCoeff ud a * SS.pauliAct (qPauli a) f x)) = _
  calc
    _ = (∑ x, (((((∑ i, Complex.normSq (ud i) : ℝ) : ℂ) / 2) *
          (star (f x) * f x)))) +
        ∑ x, ∑ a : QIndex,
          qCoeff ud a * (star (f x) * SS.pauliAct (qPauli a) f x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [mul_add, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl (fun a ha => by ring)
    _ = _ := by
      rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun a ha => by rw [Finset.mul_sum])

lemma trProj_pair (c d : SS.BitString 6 → ℂ) (P : SS.PauliString 6) :
    trProj ![c,d] P =
      SS.innerC c (SS.pauliAct P c) + SS.innerC d (SS.pauliAct P d) := by
  unfold trProj
  rw [show (Finset.univ : Finset (Fin 2)) = {0,1} by decide]
  simp

theorem q_dot_trace (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    (∑ a : QIndex,
      qCoeff (u d) a * trProj ![c,d] (qPauli a)) = (1/6 : ℂ) := by
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  have hmass : (∑ i, Complex.normSq (u d i)) = (1/6 : ℝ) := by
    simpa [r, p] using hr
  obtain ⟨hQc, hQd⟩ := Q_eigen c d hc hd hnc hnd hcode
  have hcQ : SS.innerC c (Qact (u d) c) = (1/6 : ℂ) := by
    rw [hQc, innerC_smul_right, hnc]
    norm_num
  have hdQ : SS.innerC d (Qact (u d) d) = (1/6 : ℂ) := by
    rw [hQd, innerC_smul_right, hnd]
    norm_num
  rw [inner_Q_pauli_indexed, hmass, hnc] at hcQ
  rw [inner_Q_pauli_indexed, hmass, hnd] at hdQ
  simp only [trProj_pair]
  calc
    (∑ a : QIndex, qCoeff (u d) a *
        (SS.innerC c (SS.pauliAct (qPauli a) c) +
          SS.innerC d (SS.pauliAct (qPauli a) d))) =
      (∑ a : QIndex,
        (qCoeff (u d) a * SS.innerC c (SS.pauliAct (qPauli a) c) +
          qCoeff (u d) a * SS.innerC d (SS.pauliAct (qPauli a) d))) := by
        exact Finset.sum_congr rfl (fun a ha => by ring)
    _ =
      (∑ a : QIndex,
          qCoeff (u d) a * SS.innerC c (SS.pauliAct (qPauli a) c)) +
        ∑ a : QIndex,
          qCoeff (u d) a * SS.innerC d (SS.pauliAct (qPauli a) d) := by
        rw [Finset.sum_add_distrib]
    _ = (1/6 : ℂ) := by
      norm_num at hcQ hdQ ⊢
      linear_combination hcQ + hdQ

/-- Finite complex Cauchy--Schwarz in the squared-norm convention used by
the Shor--Laflamme enumerators. -/
lemma finite_complex_cauchy {ι : Type*} [Fintype ι]
    (f g : ι → ℂ) :
    Complex.normSq (∑ i, f i * g i) ≤
      (∑ i, Complex.normSq (f i)) * (∑ i, Complex.normSq (g i)) := by
  let xf : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => star (f i))
  let xg : EuclideanSpace ℂ ι := WithLp.toLp 2 g
  have h := norm_inner_le_norm (𝕜 := ℂ) xf xg
  have hsq : ‖inner ℂ xf xg‖ ^ 2 ≤ (‖xf‖ * ‖xg‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
  have hi : inner ℂ xf xg = ∑ i, f i * g i := by
    simp only [xf, xg, PiLp.inner_apply, RCLike.inner_apply,
      starRingEnd_apply, star_star]
    exact Finset.sum_congr rfl (fun i hi => by ring)
  have hf : ‖xf‖ ^ 2 = ∑ i, Complex.normSq (f i) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [xf, norm_star, Complex.sq_norm]
  have hg : ‖xg‖ ^ 2 = ∑ i, Complex.normSq (g i) := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [xg, Complex.sq_norm]
  rw [hi, Complex.sq_norm, mul_pow, hf, hg] at hsq
  exact hsq

def lowPaulis : Finset (SS.PauliString 6) :=
  Finset.univ.filter (fun P => P.wt = 1) ∪
    Finset.univ.filter (fun P => P.wt = 2)

lemma lowPaulis_sum (psi : Fin 2 → SS.State 6 ℂ) :
    (∑ P ∈ lowPaulis, Complex.normSq (trProj psi P)) =
      Aco psi 1 + Aco psi 2 := by
  have hdis : Disjoint
      (Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 1))
      (Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 2)) := by
    rw [Finset.disjoint_left]
    intro P h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    omega
  unfold lowPaulis Aco
  exact Finset.sum_union hdis

lemma qPauli_image_subset :
    Finset.univ.image qPauli ⊆ lowPaulis := by
  intro P hP
  rw [Finset.mem_image] at hP
  obtain ⟨a, ha, rfl⟩ := hP
  rcases qPauli_weight a with h1 | h2
  · simp [lowPaulis, h1]
  · simp [lowPaulis, h2]

lemma q_trace_norm_le_A12 (psi : Fin 2 → SS.State 6 ℂ) :
    (∑ a : QIndex, Complex.normSq (trProj psi (qPauli a))) ≤
      Aco psi 1 + Aco psi 2 := by
  have himage : (∑ P ∈ Finset.univ.image qPauli,
      Complex.normSq (trProj psi P)) =
      ∑ a : QIndex, Complex.normSq (trProj psi (qPauli a)) := by
    simpa using Finset.sum_image
      (s := (Finset.univ : Finset QIndex))
      (f := fun P => Complex.normSq (trProj psi P)) qPauli_injective.injOn
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg qPauli_image_subset
    (fun P hlow hnot => Complex.normSq_nonneg (trProj psi P))
  rw [lowPaulis_sum] at hsub
  rwa [himage] at hsub

/-- The manuscript's low-weight saturation lower bound, in this library's
raw convention (`Aco_j = 4 A_j` for a two-dimensional code). -/
theorem low_bound (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    4 ≤ Aco ![c,d] 1 + Aco ![c,d] 2 := by
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  have hmass : (∑ i, Complex.normSq (u d i)) = (1/6 : ℝ) := by
    simpa [r, p] using hr
  have hqn : (∑ a : QIndex, Complex.normSq (qCoeff (u d) a)) = (1/144 : ℝ) := by
    rw [qCoeff_norm, hmass]
    norm_num
  have hdot := q_dot_trace c d hc hd hnc hnd hcode
  have hcs := finite_complex_cauchy (qCoeff (u d))
    (fun a : QIndex => trProj ![c,d] (qPauli a))
  rw [hdot, hqn] at hcs
  norm_num [Complex.normSq_div, Complex.normSq_ofReal] at hcs
  have hle := q_trace_norm_le_A12 ![c,d]
  rw [Fintype.sum_sum_type] at hle
  nlinarith

end

end SixQubit.Orbit8Universal
