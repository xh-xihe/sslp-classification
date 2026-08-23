import Mathlib
import SS.HilbertKL
import SixQubit.MacWilliams

/-!
# Shadow positivity, elementarily

Seven of the ten realized orbits whose enumerator image is known exactly need
the same external input: the zeroth Rains shadow inequality
`A_1 + A_2 + A_3 <= 1`, equivalently `Aco_1 + Aco_2 + Aco_3 <= 4` in the
unnormalized enumerator of `SixQubit/MacWilliams.lean`.

The usual derivation runs through the spin flip `Pi |-> Y^{ox n} Pi^T Y^{ox n}`,
which sends a Pauli of weight `w` to `(-1)^w` times itself, and then quotes
positivity of `Tr(Pi Pi~)`.  Formalizing that route means building the spin-flip
operator and a Pauli completeness relation.

There is a shorter way.  Summing the alternating Pauli sum over the `Z`-mask
first collapses it by `sum_chi_univ`, and what survives factors:

    sum_P (-1)^{wt P} |Tr(P Pi)|^2  =  2^n sum_{a,b} |T_{ab}|^2,
    T_{ab} = sum_u (-1)^{|u|} psi_a(u) psi_b(complement u).

The right-hand side is a sum of squared norms, so nonnegativity is immediate and
no operator, transpose or matrix positivity is needed.  Both sides are computed
down to the common quantity `core`.

This file carries the definitions and the elementary half; the Fourier half
meets it at `core`.
-/

namespace SS.Shadow

open SS.MacWilliams

variable {n K : ℕ}

/-! ## Four-fold interchange

The elementary half is one interchange of summation order, but at depth four,
where `Finset.sum_comm` alone does not reach. -/

lemma sum4_comm {M : Type*} [AddCommMonoid M] {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (f : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d
      = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        calc ∑ a, ∑ b, ∑ d, f a b c d
            = ∑ a, ∑ d, ∑ b, f a b c d :=
              Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
          _ = ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_comm

/-! ## The sign and the pairing -/

/-- The all-ones mask. -/
def ones (n : ℕ) : SS.BitString n := fun _ => true

/-- `(-1)^{|u|}`, written through `chi` so that the existing sign lemmas apply
without a separate parity development. -/
def psign (u : SS.BitString n) : ℝ := chi u (ones n)

lemma psign_bxor (u v : SS.BitString n) :
    psign (SS.bxor u v) = psign u * psign v :=
  chi_bxor_left u v (ones n)

@[simp] lemma psign_star (u : SS.BitString n) :
    star ((psign u : ℝ) : ℂ) = ((psign u : ℝ) : ℂ) := by
  simp

/-- The bilinear pairing whose squared norms make the shadow sum manifestly
nonnegative.  It is bilinear, not sesquilinear: no conjugate appears. -/
noncomputable def Tf (psi : Fin K → SS.State n ℂ) (a b : Fin K) : ℂ :=
  ∑ u, ((psign u : ℝ) : ℂ) * psi a u * psi b (SS.complement u)

/-- The quantity both computations reduce to. -/
noncomputable def core (psi : Fin K → SS.State n ℂ) : ℂ :=
  ∑ u, ∑ v, ((psign u : ℝ) : ℂ) * ((psign v : ℝ) : ℂ)
      * RR psi u v * RR psi (SS.complement u) (SS.complement v)

/-! ## The elementary half: `core` is a sum of squared norms -/

lemma star_Tf (psi : Fin K → SS.State n ℂ) (a b : Fin K) :
    star (Tf psi a b)
      = ∑ v, ((psign v : ℝ) : ℂ) * star (psi a v) * star (psi b (SS.complement v)) := by
  unfold Tf
  rw [star_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [star_mul', psign_star]

lemma normSq_Tf_expand (psi : Fin K → SS.State n ℂ) (a b : Fin K) :
    ((Complex.normSq (Tf psi a b) : ℝ) : ℂ)
      = ∑ u, ∑ v, (((psign u : ℝ) : ℂ) * psi a u * psi b (SS.complement u))
          * (((psign v : ℝ) : ℂ) * star (psi a v) * star (psi b (SS.complement v))) := by
  have h : ((Complex.normSq (Tf psi a b) : ℝ) : ℂ) = Tf psi a b * star (Tf psi a b) := by
    rw [Complex.star_def]
    exact (Complex.mul_conj _).symm
  rw [h, star_Tf]
  conv_lhs => rw [Tf]
  exact Finset.sum_mul_sum _ _ _ _

theorem core_eq_sum_normSq (psi : Fin K → SS.State n ℂ) :
    core psi = ∑ a, ∑ b, ((Complex.normSq (Tf psi a b) : ℝ) : ℂ) := by
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => normSq_Tf_expand psi a b))]
  rw [sum4_comm (fun a b u v =>
    (((psign u : ℝ) : ℂ) * psi a u * psi b (SS.complement u))
      * (((psign v : ℝ) : ℂ) * star (psi a v) * star (psi b (SS.complement v))))]
  unfold core RR
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
  have h2 : (∑ a, psi a u * star (psi a v))
        * (∑ b, psi b (SS.complement u) * star (psi b (SS.complement v)))
      = ∑ a, ∑ b, (psi a u * star (psi a v))
          * (psi b (SS.complement u) * star (psi b (SS.complement v))) :=
    Finset.sum_mul_sum _ _ _ _
  rw [mul_assoc (((psign u : ℝ) : ℂ) * ((psign v : ℝ) : ℂ)), h2, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `core` is a nonnegative real: it is a sum of squared norms. -/
theorem core_eq_nonneg_real (psi : Fin K → SS.State n ℂ) :
    core psi = ((∑ a, ∑ b, Complex.normSq (Tf psi a b) : ℝ) : ℂ)
      ∧ 0 ≤ (∑ a, ∑ b, Complex.normSq (Tf psi a b) : ℝ) := by
  refine ⟨?_, Finset.sum_nonneg (fun a _ =>
    Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _))⟩
  rw [core_eq_sum_normSq]
  push_cast
  rfl

/-! ## The Pauli sign, factored

`(-1)^{wt P}` has to be split into a factor depending only on the `X`-mask and
one depending on the `Z`-mask, or the `Z`-sum cannot be done first.  The split
is `|x or z| = |x| + |z and not x|`, checked one coordinate at a time. -/

lemma altsign_factor (P : SS.PauliString n) :
    ((-1 : ℝ)) ^ P.wt = chi P.x (ones n) * chi P.z (SS.complement P.x) := by
  have hprod : chi P.x (ones n) * chi P.z (SS.complement P.x)
      = ∏ i, (if P.x i || P.z i then (-1 : ℝ) else 1) := by
    rw [chi, chi, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [ones, SS.complement]
    rcases Bool.eq_false_or_eq_true (P.x i) with hx | hx <;>
      rcases Bool.eq_false_or_eq_true (P.z i) with hz | hz <;>
        simp [hx, hz]
  rw [hprod, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    wt_eq_card_supp, supp]

/-! ## The matrix elements, rewritten through the projector matrix -/

/-- The Knill--Laflamme sum with the `i^{#Y}` prefactor stripped, expressed
through the projector matrix `RR`. -/
theorem melTr_eq_RR (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    melTr psi P = ∑ s, ((chi P.z s : ℝ) : ℂ) * RR psi s (SS.bxor s P.x) := by
  unfold melTr mel RR
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  ring

/-! ## Expanding one squared matrix element -/

lemma star_melTr_eq (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    star (melTr psi P) = ∑ t, ((chi P.z t : ℝ) : ℂ) * RR psi (SS.bxor t P.x) t := by
  rw [melTr_eq_RR, star_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [star_mul', star_RR, Complex.star_def, Complex.conj_ofReal]

lemma normSq_melTr_expand (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    ((Complex.normSq (melTr psi P) : ℝ) : ℂ)
      = ∑ s, ∑ t, ((chi P.z s : ℝ) : ℂ) * ((chi P.z t : ℝ) : ℂ)
          * RR psi s (SS.bxor s P.x) * RR psi (SS.bxor t P.x) t := by
  have h : ((Complex.normSq (melTr psi P) : ℝ) : ℂ)
      = melTr psi P * star (melTr psi P) := by
    rw [Complex.star_def]
    exact (Complex.mul_conj _).symm
  rw [h, star_melTr_eq]
  conv_lhs => rw [melTr_eq_RR]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => by ring))

end SS.Shadow
