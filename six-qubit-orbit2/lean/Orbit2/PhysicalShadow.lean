import Mathlib
import SS.HilbertKL
import Orbit2.PhysicalMacWilliams

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
    simp only [SS.ones, SS.complement]
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

/-! ## Two bitstring identities

These are what turn the surviving index `t = s + xbar` into a complement, which
is how the `x`-sum reassembles into `core`. -/

lemma bxor_complement_right (s x : SS.BitString n) :
    SS.bxor s (SS.complement x) = SS.complement (SS.bxor s x) := by
  funext i
  have : ∀ p q : Bool, xor p (!q) = !(xor p q) := by decide
  simpa only [SS.bxor_apply, SS.complement] using this (s i) (x i)

lemma bxor_complement_self (s x : SS.BitString n) :
    SS.bxor (SS.bxor s (SS.complement x)) x = SS.complement s := by
  funext i
  have : ∀ p q : Bool, xor (xor p (!q)) q = !p := by decide
  simpa only [SS.bxor_apply, SS.complement] using this (s i) (x i)

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

/-! ## The `Z`-sum, collapsed

This is the step that makes the whole argument elementary.  Doing the `Z`-sum
first turns the three characters into one, `sum_chi_univ` kills every term but
those with `t = s + xbar`, and the surviving index is a complement. -/

lemma z_sum_collapse (psi : Fin K → SS.State n ℂ) (x : SS.BitString n) :
    ∑ z, ((chi z (SS.complement x) : ℝ) : ℂ)
        * ((Complex.normSq (melTr psi ⟨x, z⟩) : ℝ) : ℂ)
      = (2 : ℂ) ^ n * ∑ s, RR psi s (SS.bxor s x)
          * RR psi (SS.complement s) (SS.complement (SS.bxor s x)) := by
  classical
  have step1 : ∀ z : SS.BitString n,
      ((chi z (SS.complement x) : ℝ) : ℂ)
          * ((Complex.normSq (melTr psi ⟨x, z⟩) : ℝ) : ℂ)
        = ∑ s, ∑ t,
            ((chi z (SS.bxor (SS.complement x) (SS.bxor s t)) : ℝ) : ℂ)
              * (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t) := by
    intro z
    rw [normSq_melTr_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [chi_bxor_right, chi_bxor_right]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => step1 z), Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_comm]
  -- the `z`-sum, for fixed `s` and `t`
  have hz : ∀ t : SS.BitString n,
      ∑ z, ((chi z (SS.bxor (SS.complement x) (SS.bxor s t)) : ℝ) : ℂ)
            * (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t)
        = (if t = SS.bxor s (SS.complement x)
           then (2 : ℂ) ^ n * (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t)
           else 0) := by
    intro t
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_chi_univ]
    by_cases h : t = SS.bxor s (SS.complement x)
    · rw [if_pos ((bxor_triple_zero_iff _ _ _).mpr h), if_pos h]
      push_cast
      ring
    · rw [if_neg (fun hc => h ((bxor_triple_zero_iff _ _ _).mp hc)), if_neg h]
      simp
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => hz t),
    Finset.sum_ite_eq' Finset.univ (SS.bxor s (SS.complement x))
      (fun t => (2 : ℂ) ^ n * (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t)),
    if_pos (Finset.mem_univ _), bxor_complement_self, bxor_complement_right]

/-! ## Assembly: the alternating Pauli sum is `2^n` times `core` -/

lemma bxor_cancel (s v : SS.BitString n) : SS.bxor s (SS.bxor s v) = v := by
  funext i
  have : ∀ p q : Bool, xor p (xor p q) = q := by decide
  simpa only [SS.bxor_apply] using this (s i) (v i)

theorem alt_sum_eq_core (psi : Fin K → SS.State n ℂ) :
    ∑ P : SS.PauliString n,
        ((((-1 : ℝ)) ^ P.wt * Complex.normSq (trProj psi P) : ℝ) : ℂ)
      = (2 : ℂ) ^ n * core psi := by
  classical
  have hterm : ∀ x z : SS.BitString n,
      ((((-1 : ℝ)) ^ (⟨x, z⟩ : SS.PauliString n).wt
          * Complex.normSq (trProj psi ⟨x, z⟩) : ℝ) : ℂ)
        = ((chi x (ones n) : ℝ) : ℂ)
            * (((chi z (SS.complement x) : ℝ) : ℂ)
              * ((Complex.normSq (melTr psi ⟨x, z⟩) : ℝ) : ℂ)) := by
    intro x z
    rw [altsign_factor, normSq_trProj]
    push_cast
    ring
  rw [sum_pauli, Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => hterm x z))]
  have hx : ∀ x : SS.BitString n,
      ∑ z, ((chi x (ones n) : ℝ) : ℂ)
          * (((chi z (SS.complement x) : ℝ) : ℂ)
            * ((Complex.normSq (melTr psi ⟨x, z⟩) : ℝ) : ℂ))
        = ((chi x (ones n) : ℝ) : ℂ) * ((2 : ℂ) ^ n
            * ∑ s, RR psi s (SS.bxor s x)
                * RR psi (SS.complement s) (SS.complement (SS.bxor s x))) := by
    intro x
    rw [← Finset.mul_sum, z_sum_collapse psi x]
  have hy : ∀ x : SS.BitString n,
      ((chi x (ones n) : ℝ) : ℂ) * ((2 : ℂ) ^ n
          * ∑ s, RR psi s (SS.bxor s x)
              * RR psi (SS.complement s) (SS.complement (SS.bxor s x)))
        = (2 : ℂ) ^ n * ∑ s, ((chi x (ones n) : ℝ) : ℂ)
            * (RR psi s (SS.bxor s x)
              * RR psi (SS.complement s) (SS.complement (SS.bxor s x))) := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun (s : SS.BitString n) _ => by ring)
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => (hx x).trans (hy x)),
    ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm, core]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← sum_bxor_reindex' (M := ℂ) s (fun x => ((chi x (ones n) : ℝ) : ℂ)
    * (RR psi s (SS.bxor s x)
      * RR psi (SS.complement s) (SS.complement (SS.bxor s x))))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [bxor_cancel, show chi (SS.bxor s v) (ones n) = psign s * psign v from
    psign_bxor s v]
  push_cast
  ring

/-- **Shadow positivity.**  The alternating Pauli sum is nonnegative, because it
is `2^n` times a sum of squared norms.  No spin-flip operator, transpose or
matrix positivity appears. -/
theorem alt_sum_nonneg (psi : Fin K → SS.State n ℂ) :
    0 ≤ ∑ P : SS.PauliString n,
        ((-1 : ℝ)) ^ P.wt * Complex.normSq (trProj psi P) := by
  have h := alt_sum_eq_core psi
  rw [core_eq_sum_normSq] at h
  have hcast : ((∑ P : SS.PauliString n,
        ((-1 : ℝ)) ^ P.wt * Complex.normSq (trProj psi P) : ℝ) : ℂ)
      = (((2 : ℝ) ^ n * ∑ a, ∑ b, Complex.normSq (Tf psi a b) : ℝ) : ℂ) := by
    push_cast
    push_cast at h
    exact h
  rw [Complex.ofReal_inj.mp hcast]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _)))

/-! ## The six-qubit consequence

Grouping the alternating Pauli sum by weight turns it into the alternating
enumerator sum, and the six-qubit MacWilliams normal form already in
`SixQubit/MacWilliams.lean` collapses that to `32 - 8(A_1 + A_2 + A_3)`.
Positivity is then the zeroth Rains shadow inequality. -/

set_option maxRecDepth 8000 in
lemma alt_sum_as_Aco (psi : Fin K → SS.State 6 ℂ) :
    ∑ P : SS.PauliString 6, ((-1 : ℝ)) ^ P.wt * Complex.normSq (trProj psi P)
      = ∑ k ∈ Finset.range 7, ((-1 : ℝ)) ^ k * Aco psi k := by
  classical
  have hmap : ∀ P ∈ (Finset.univ : Finset (SS.PauliString 6)),
      P.wt ∈ Finset.range 7 := by
    intro P _
    rw [Finset.mem_range, wt_eq_card_supp]
    have h : (supp P).card ≤ 6 := by simpa using Finset.card_le_univ (supp P)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun P => ((-1 : ℝ)) ^ P.wt * Complex.normSq (trProj psi P))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Aco, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2])

set_option maxRecDepth 8000 in
/-- **The zeroth Rains shadow inequality at six qubits.**

For an exact `((6,2,d>=3))` code, `A_1 + A_2 + A_3 <= 1` in the normalized
enumerator; here in the unnormalized one, where `A_0 = 4`. -/
theorem shadow_bound (psi : Fin 2 → SS.State 6 ℂ) (hd3 : SS.HasDistance psi 3)
    (hA0 : Aco psi 0 = 4) :
    Aco psi 1 + Aco psi 2 + Aco psi 3 ≤ 4 := by
  obtain ⟨h4, h5, h6⟩ := macwilliams_six psi hd3 hA0
  have hpos := alt_sum_nonneg psi
  rw [alt_sum_as_Aco] at hpos
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, one_mul] at hpos
  norm_num at hpos
  rw [h4, h5, h6, hA0] at hpos
  linarith

end SS.Shadow
