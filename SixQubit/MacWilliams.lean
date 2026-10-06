import Mathlib

import SS.Pauli
import SS.FullKL
import SS.HilbertKL
import SixQubit.Orbit36Enum
import SixQubit.Orbit36Class
import SixQubit.Orbit36Code
import SixQubit.CodeEquiv

/-!
# The quantum MacWilliams identity for Shor--Laflamme enumerators

For a code projector `Pi` on `n` qubits the Shor--Laflamme enumerators are

    A_j = (1/K^2) * sum_{wt E = j} |Tr (E Pi)|^2,
    B_j = (1/K)   * sum_{wt E = j} Tr (E Pi E^dagger Pi),

and the MacWilliams transform expresses `B` from `A`.  This module proves that
transform, in a form that needs no operator algebra: everything is phrased in
the Hilbert-space semantics of `SS.HilbertKL`, so a "code" is nothing but a
family `psi : Fin K -> SS.State n C` and the two enumerators are

    `trProj psi P = sum_a <psi_a| P |psi_a>`            (`Tr (P Pi)`),
    `frob  psi P = sum_{a,b} |<psi_a| P |psi_b>|^2`     (`Tr (P Pi P^dag Pi)`).

## What is proved, and how

*Section 1--2, the Walsh character.*  `chi u v = (-1)^{u.v}` is defined as a
product over the qubits, which makes bilinearity a coordinatewise Boolean check
and makes character orthogonality an instance of `Finset.prod_univ_sum`:
summing `chi . u` over the sub-cube of bitstrings supported in `S` gives
`2^{|S|}` when `u` vanishes on `S` and `0` otherwise (`sum_chi_cube`).
`signC_bdot` is the bridge to the repository's `SS.bdot` sign convention.

*Section 3--7, the duality step.*  `pauli_duality` is the Parseval half of the
MacWilliams identity:

    sum_{Q} (-1)^{<P,Q>} |Tr (Q Pi)|^2 = 2^n * Tr (P Pi P^dag Pi),

where `<P,Q>` is the commutation form.  It holds for an *arbitrary* family
`psi` -- no orthonormality, no code condition, no distance.  The proof expands
both sides into a fourfold bitstring sum, kills the `z`-sum with character
orthogonality and reindexes; the common normal form is `core`.  The unit
prefactor `i^{#Y}` of `SS.pauliAct` never has to be computed, because both
sides are moduli.

*Section 8--9, the subset form.*  Summing the duality over all Paulis supported
inside a set `S` of qubits factors the sign sum through two sub-cubes and gives
`subset_duality`.  This is the form the classical proof would call
"MacWilliams with a Krawtchouk-free weight enumerator": no Krawtchouk
polynomial is ever needed, because the *product* sets `supp P subseteq S` --
unlike the weight classes -- have a completely elementary sign sum.

*Section 10--12.*  The Knill--Laflamme condition for `P` says
`Tr (P Pi P^dag Pi) = |Tr (P Pi)|^2 / K` (`frob_of_KL`).  Feeding that into the
subset form for every `S` gives `subset_macwilliams`, a relation purely among
the `A`-weights, valid whenever the code detects every Pauli supported in `S`.

*Section 13--16.*  Averaging `subset_macwilliams` over all `m`-element sets of
qubits, `m = 0, 1, 2`, turns it into three linear relations among
`A_0, ..., A_6`.  The two combinatorial counts that appear -- how many
`m`-sets contain a given support, and how many are disjoint from it -- are
finite checks over `Finset (Fin 6)` (64 elements), certified by `decide`.
`macwilliams_six` is the resulting normal form of a `((6,2,3))` code:

    A_4 = 15 - 4 A_2 - 3 A_3,
    A_5 = 12 + 3 A_1 + 4 A_2 + 3 A_3,
    A_6 =  4 - 4 A_1 -   A_2 -   A_3.

*Section 17.*  These are exactly the three hypotheses `hmw4`, `hmw5`, `hmw6`
of `SixQubit.Orbit36Enum.unique_enumerator`, so the chapter's last conditional
step closes: `Orbit36MacWilliams.orbit36_enumerator` derives the full vector
`(1, 0, 21/25, 0, 291/25, 384/25, 79/25)` for an arbitrary exact orbit-36
solution from the support conditions, one `MomentSystem` and the twenty-two
Knill--Laflamme rows alone.

The distance-three input is not assumed either: an orbit-36 solution is
equivalent to the canonical representative by `Orbit36Class.orbit36_theorem`,
and `Orbit36Code.canonical_is_code` says the representative is a code, so
`hasDistance_of_orbit36` supplies `SS.HasDistance ![c, d] 3`.

No `sorry`, no `native_decide`.
-/

namespace SS
namespace MacWilliams

open scoped BigOperators
open Finset

set_option maxRecDepth 10000

variable {n : ℕ}

/-! ## 1.  The Walsh character of a pair of bitstrings -/

/-- `chi u v = (-1)^(u . v)`, written as a product so that bilinearity is a
one-line coordinatewise check. -/
def chi (u v : SS.BitString n) : ℝ := ∏ i, (if u i && v i then (-1 : ℝ) else 1)

lemma chi_comm (u v : SS.BitString n) : chi u v = chi v u := by
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Bool.and_comm]

lemma chi_bxor_left (s t u : SS.BitString n) :
    chi (SS.bxor s t) u = chi s u * chi t u := by
  rw [chi, chi, chi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [SS.bxor_apply]
  rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;>
    rcases Bool.eq_false_or_eq_true (t i) with ht | ht <;>
      rcases Bool.eq_false_or_eq_true (u i) with hu | hu <;>
        simp only [hs, ht, hu] <;> norm_num

lemma chi_bxor_right (u s t : SS.BitString n) :
    chi u (SS.bxor s t) = chi u s * chi u t := by
  rw [chi_comm, chi_bxor_left, chi_comm s u, chi_comm t u]

lemma chi_eq_pow (u v : SS.BitString n) :
    chi u v = (-1 : ℝ) ^ ((Finset.univ.filter (fun i => u i && v i)).card) := by
  rw [chi, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- The bridge to the repository's `SS.bdot` sign convention. -/
lemma signC_bdot (u v : SS.BitString n) (t : ℂ) :
    SS.signC (SS.bdot u v) t = (chi u v : ℂ) * t := by
  have hpow := chi_eq_pow u v
  rcases Nat.even_or_odd ((Finset.univ.filter (fun i => u i && v i)).card) with he | ho
  · have h1 : SS.bdot u v = false := by
      have hz : ((Finset.univ.filter (fun i => u i && v i)).card) % 2 = 0 := Nat.even_iff.mp he
      simp only [SS.bdot, hz]
      rfl
    rw [h1, hpow, he.neg_one_pow, SS.signC_false]
    push_cast
    rw [one_mul]
  · have h1 : SS.bdot u v = true := by
      have hz : ((Finset.univ.filter (fun i => u i && v i)).card) % 2 = 1 := Nat.odd_iff.mp ho
      simp only [SS.bdot, hz]
      rfl
    rw [h1, hpow, ho.neg_one_pow, SS.signC_true]
    push_cast
    ring

/-! ## 2.  Sub-cubes of bitstrings and partial character orthogonality -/

/-- The bitstrings supported inside `S`. -/
def cube (S : Finset (Fin n)) : Finset (SS.BitString n) :=
  Fintype.piFinset (fun i => if i ∈ S then (Finset.univ : Finset Bool) else {false})

lemma mem_cube {S : Finset (Fin n)} {x : SS.BitString n} :
    x ∈ cube S ↔ ∀ i, i ∉ S → x i = false := by
  rw [cube, Fintype.mem_piFinset]
  constructor
  · intro h i hi
    have := h i
    rw [if_neg hi, Finset.mem_singleton] at this
    exact this
  · intro h i
    by_cases hi : i ∈ S
    · rw [if_pos hi]; exact Finset.mem_univ _
    · rw [if_neg hi, Finset.mem_singleton]; exact h i hi

@[simp] lemma cube_univ : cube (Finset.univ : Finset (Fin n)) = Finset.univ := by
  ext x
  simp [mem_cube]

/-- **Partial character orthogonality.**  Summing `chi · u` over the sub-cube
indexed by `S` gives `2^{|S|}` when `u` vanishes on `S`, and `0` otherwise. -/
lemma sum_chi_cube (S : Finset (Fin n)) (u : SS.BitString n) :
    ∑ x ∈ cube S, chi x u = if ∀ i ∈ S, u i = false then (2 : ℝ) ^ S.card else 0 := by
  classical
  have key : ∑ x ∈ cube S, chi x u
      = ∏ i : Fin n, ∑ b ∈ (if i ∈ S then (Finset.univ : Finset Bool) else {false}),
          (if b && u i then (-1 : ℝ) else 1) := by
    rw [Finset.prod_univ_sum]
    rfl
  have hfac : ∀ i : Fin n,
      (∑ b ∈ (if i ∈ S then (Finset.univ : Finset Bool) else {false}),
          (if b && u i then (-1 : ℝ) else 1))
        = if i ∈ S then (if u i then 0 else 2) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · rw [if_pos hi, if_pos hi, Fintype.sum_bool]
      cases hu : u i <;> norm_num
    · rw [if_neg hi, if_neg hi, Finset.sum_singleton]
      simp
  rw [key, Finset.prod_congr rfl (fun i _ => hfac i)]
  by_cases hu : ∀ i ∈ S, u i = false
  · rw [if_pos hu]
    have : ∀ i : Fin n, (if i ∈ S then (if u i then (0 : ℝ) else 2) else 1)
        = if i ∈ S then (2 : ℝ) else 1 := by
      intro i
      by_cases hi : i ∈ S
      · rw [if_pos hi, if_pos hi, hu i hi]; norm_num
      · rw [if_neg hi, if_neg hi]
    rw [Finset.prod_congr rfl (fun i _ => this i), Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one, Finset.filter_mem_eq_inter, Finset.univ_inter]
  · rw [if_neg hu]
    push_neg at hu
    obtain ⟨i, hiS, hui⟩ := hu
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [if_pos hiS, if_pos (by simpa using hui)]

/-- Full character orthogonality. -/
lemma sum_chi_univ (u : SS.BitString n) :
    ∑ x : SS.BitString n, chi x u
      = if u = (fun _ => false) then (2 : ℝ) ^ n else 0 := by
  have := sum_chi_cube (Finset.univ : Finset (Fin n)) u
  rw [cube_univ] at this
  rw [this]
  by_cases hu : u = (fun _ => false)
  · rw [if_pos hu, if_pos (by intro i _; rw [hu])]
    simp
  · rw [if_neg hu, if_neg]
    intro h
    exact hu (funext (fun i => h i (Finset.mem_univ i)))

/-! ## 3.  Bitstring bookkeeping -/

lemma bxor_right_comm (s a b : SS.BitString n) :
    SS.bxor (SS.bxor s a) b = SS.bxor (SS.bxor s b) a := by
  have key : ∀ p q r : Bool, xor (xor p q) r = xor (xor p r) q := by decide
  funext i
  simpa only [SS.bxor_apply] using key (s i) (a i) (b i)

lemma bxor_triple_zero_iff (a s t : SS.BitString n) :
    SS.bxor a (SS.bxor s t) = (fun _ => false) ↔ t = SS.bxor s a := by
  have key : ∀ p q r : Bool, (xor p (xor q r) = false) ↔ r = xor q p := by decide
  constructor
  · intro h
    funext i
    have hi : xor (a i) (xor (s i) (t i)) = false := by
      simpa only [SS.bxor_apply] using congrFun h i
    simpa only [SS.bxor_apply] using (key (a i) (s i) (t i)).mp hi
  · intro h
    funext i
    have hi : t i = xor (s i) (a i) := by
      simpa only [SS.bxor_apply] using congrFun h i
    simpa only [SS.bxor_apply] using (key (a i) (s i) (t i)).mpr hi

/-- Reindexing a full bitstring sum by XOR with a fixed mask. -/
lemma sum_bxor_reindex {M : Type*} [AddCommMonoid M] (x : SS.BitString n)
    (f : SS.BitString n → M) :
    ∑ s : SS.BitString n, f (SS.bxor s x) = ∑ s : SS.BitString n, f s :=
  Fintype.sum_equiv (SS.bxorEquiv x) _ _ (fun _ => rfl)

/-- Full character orthogonality, complex form. -/
lemma sum_chi_univ_C (u : SS.BitString n) :
    ∑ x : SS.BitString n, ((chi x u : ℝ) : ℂ)
      = if u = (fun _ => false) then (2 : ℂ) ^ n else 0 := by
  rw [← Complex.ofReal_sum, sum_chi_univ]
  by_cases hu : u = (fun _ => false)
  · rw [if_pos hu, if_pos hu]; push_cast; ring
  · rw [if_neg hu, if_neg hu]; norm_num

/-! ## 4.  Pauli sums as double bitstring sums -/

/-- A Pauli string is exactly a pair of bitstrings. -/
def pauliEquiv : SS.PauliString n ≃ SS.BitString n × SS.BitString n where
  toFun P := (P.x, P.z)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

lemma sum_pauli {M : Type*} [AddCommMonoid M] (f : SS.PauliString n → M) :
    ∑ P : SS.PauliString n, f P
      = ∑ x : SS.BitString n, ∑ z : SS.BitString n, f ⟨x, z⟩ := by
  rw [Fintype.sum_equiv pauliEquiv f (fun p => f ⟨p.1, p.2⟩) (fun _ => rfl),
    Fintype.sum_prod_type]

/-! ## 5.  The two Shor--Laflamme quantities -/

variable {K : ℕ}

noncomputable section

/-- `Tr (P * Pi)` for the projector `Pi` onto the span of an orthonormal family
`psi`, in the Hilbert-space semantics of `SS.HilbertKL`. -/
def trProj (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) : ℂ :=
  ∑ a, SS.innerC (psi a) (SS.pauliAct P (psi a))

/-- `Tr (P * Pi * P^dagger * Pi)`, written as the squared Frobenius norm of the
Knill--Laflamme matrix of `P`. -/
def frob (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) : ℝ :=
  ∑ a, ∑ b, Complex.normSq (SS.innerC (psi a) (SS.pauliAct P (psi b)))

/-- The matrix element with the unit prefactor `i^{#Y}` stripped off. -/
def mel (u v : SS.State n ℂ) (P : SS.PauliString n) : ℂ :=
  ∑ s, ((chi P.z s : ℝ) : ℂ) * (star (u (SS.bxor s P.x)) * v s)

/-- The projector trace with the unit prefactor stripped off. -/
def melTr (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) : ℂ :=
  ∑ a, mel (psi a) (psi a) P

/-- The one-body correlation matrix of the family `psi`, i.e. the matrix of the
projector `Pi` in the computational basis. -/
def RR (psi : Fin K → SS.State n ℂ) (p q : SS.BitString n) : ℂ :=
  ∑ a, psi a p * star (psi a q)

lemma star_RR (psi : Fin K → SS.State n ℂ) (p q : SS.BitString n) :
    star (RR psi p q) = RR psi q p := by
  rw [RR, RR, star_sum]
  exact Finset.sum_congr rfl (fun a _ => by rw [star_mul', star_star, mul_comm])

lemma innerC_eq_mel (u v : SS.State n ℂ) (P : SS.PauliString n) :
    SS.innerC u (SS.pauliAct P v) = Complex.I ^ P.numY * mel u v P := by
  rw [SS.innerC_pauliAct, mel]
  exact congrArg _ (Finset.sum_congr rfl (fun s _ => signC_bdot _ _ _))

lemma normSq_I_pow_mul (k : ℕ) (t : ℂ) :
    Complex.normSq (Complex.I ^ k * t) = Complex.normSq t := by
  rw [map_mul, map_pow, Complex.normSq_I, one_pow, one_mul]

lemma normSq_innerC (u v : SS.State n ℂ) (P : SS.PauliString n) :
    Complex.normSq (SS.innerC u (SS.pauliAct P v)) = Complex.normSq (mel u v P) := by
  rw [innerC_eq_mel, normSq_I_pow_mul]

lemma trProj_eq (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    trProj psi P = Complex.I ^ P.numY * melTr psi P := by
  rw [trProj, melTr, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => innerC_eq_mel _ _ _)

lemma normSq_trProj (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    Complex.normSq (trProj psi P) = Complex.normSq (melTr psi P) := by
  rw [trProj_eq, normSq_I_pow_mul]

lemma normSq_cast (z : ℂ) : ((Complex.normSq z : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def]
  exact (Complex.mul_conj z).symm

lemma melTr_eq_RR (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    melTr psi P = ∑ s, ((chi P.z s : ℝ) : ℂ) * RR psi s (SS.bxor s P.x) := by
  rw [melTr]
  simp only [mel]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [RR, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun a _ => by ring)

lemma bxor_cancel_left (s y : SS.BitString n) : SS.bxor s (SS.bxor s y) = y := by
  have key : ∀ p q : Bool, xor p (xor p q) = q := by decide
  funext i
  simpa only [SS.bxor_apply] using key (s i) (y i)

lemma sum_bxor_reindex' {M : Type*} [AddCommMonoid M] (x : SS.BitString n)
    (f : SS.BitString n → M) :
    ∑ s : SS.BitString n, f (SS.bxor x s) = ∑ s : SS.BitString n, f s := by
  rw [← sum_bxor_reindex x f]
  exact Finset.sum_congr rfl (fun s _ => by rw [SS.bxor_comm])

lemma sum_comm4 {M : Type*} [AddCommMonoid M] {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d
      = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => Finset.sum_comm))
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

/-! ## 6.  The Fourier core -/

lemma star_melTr (psi : Fin K → SS.State n ℂ) (Q : SS.PauliString n) :
    star (melTr psi Q)
      = ∑ t, ((chi Q.z t : ℝ) : ℂ) * RR psi (SS.bxor t Q.x) t := by
  rw [melTr_eq_RR, star_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [star_mul', star_RR, Complex.star_def, Complex.conj_ofReal]

lemma melTr_mul_star (psi : Fin K → SS.State n ℂ) (Q : SS.PauliString n) :
    melTr psi Q * star (melTr psi Q)
      = ∑ s, ∑ t, ((chi Q.z (SS.bxor s t) : ℝ) : ℂ)
          * (RR psi s (SS.bxor s Q.x) * RR psi (SS.bxor t Q.x) t) := by
  rw [star_melTr, melTr_eq_RR, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
  rw [chi_bxor_right]
  push_cast
  ring

/-- The common normal form reached from both sides of the duality. -/
def core (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) : ℂ :=
  ∑ y : SS.BitString n, ∑ s : SS.BitString n,
    ((chi P.z y : ℝ) : ℂ)
      * (RR psi s (SS.bxor s y) * RR psi (SS.bxor (SS.bxor s P.x) y) (SS.bxor s P.x))

lemma lhs_eq_core (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    ∑ Q : SS.PauliString n,
        (((chi P.x Q.z : ℝ) : ℂ) * ((chi P.z Q.x : ℝ) : ℂ))
          * (melTr psi Q * star (melTr psi Q))
      = (2 : ℂ) ^ n * core psi P := by
  classical
  rw [sum_pauli, core, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have expand : ∀ qz : SS.BitString n,
      (((chi P.x qz : ℝ) : ℂ) * ((chi P.z y : ℝ) : ℂ))
          * (melTr psi ⟨y, qz⟩ * star (melTr psi ⟨y, qz⟩))
        = ∑ s : SS.BitString n, ∑ t : SS.BitString n,
            ((chi qz (SS.bxor P.x (SS.bxor s t)) : ℝ) : ℂ)
              * (((chi P.z y : ℝ) : ℂ)
                  * (RR psi s (SS.bxor s y) * RR psi (SS.bxor t y) t)) := by
    intro qz
    rw [melTr_mul_star, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [chi_bxor_right qz P.x (SS.bxor s t), chi_bxor_right qz s t, chi_comm P.x qz]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun qz _ => expand qz), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_comm]
  have inner : ∀ t : SS.BitString n,
      (∑ qz : SS.BitString n, ((chi qz (SS.bxor P.x (SS.bxor s t)) : ℝ) : ℂ)
          * (((chi P.z y : ℝ) : ℂ)
              * (RR psi s (SS.bxor s y) * RR psi (SS.bxor t y) t)))
        = if t = SS.bxor s P.x then
            (2 : ℂ) ^ n * (((chi P.z y : ℝ) : ℂ)
              * (RR psi s (SS.bxor s y) * RR psi (SS.bxor t y) t)) else 0 := by
    intro t
    rw [← Finset.sum_mul, sum_chi_univ_C]
    by_cases h : SS.bxor P.x (SS.bxor s t) = (fun _ => false)
    · rw [if_pos h, if_pos ((bxor_triple_zero_iff P.x s t).mp h)]
    · rw [if_neg h, if_neg (fun hc => h ((bxor_triple_zero_iff P.x s t).mpr hc)), zero_mul]
  rw [Finset.sum_congr rfl (fun t _ => inner t), Fintype.sum_ite_eq']

lemma rhs_eq_core (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    ∑ a, ∑ b, (mel (psi a) (psi b) P * star (mel (psi a) (psi b) P)) = core psi P := by
  classical
  have hstar : ∀ a b : Fin K, star (mel (psi a) (psi b) P)
      = ∑ t, ((chi P.z t : ℝ) : ℂ) * (psi a (SS.bxor t P.x) * star (psi b t)) := by
    intro a b
    rw [mel, star_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [star_mul', star_mul', star_star, Complex.star_def, Complex.conj_ofReal]
  have hprod : ∀ a b : Fin K,
      mel (psi a) (psi b) P * star (mel (psi a) (psi b) P)
        = ∑ s : SS.BitString n, ∑ t : SS.BitString n,
            (((chi P.z s : ℝ) : ℂ) * ((chi P.z t : ℝ) : ℂ))
              * ((star (psi a (SS.bxor s P.x)) * psi a (SS.bxor t P.x))
                  * (psi b s * star (psi b t))) := by
    intro a b
    rw [hstar a b, mel, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => by ring))
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hprod a b))]
  rw [sum_comm4]
  have hab : ∀ s t : SS.BitString n,
      (∑ a : Fin K, ∑ b : Fin K,
          (((chi P.z s : ℝ) : ℂ) * ((chi P.z t : ℝ) : ℂ))
            * ((star (psi a (SS.bxor s P.x)) * psi a (SS.bxor t P.x))
                * (psi b s * star (psi b t))))
        = ((chi P.z (SS.bxor s t) : ℝ) : ℂ)
            * (RR psi (SS.bxor t P.x) (SS.bxor s P.x) * RR psi s t) := by
    intro s t
    rw [chi_bxor_right, RR, RR, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => hab s t))]
  have hcore : core psi P = ∑ s : SS.BitString n, ∑ y : SS.BitString n,
      ((chi P.z y : ℝ) : ℂ)
        * (RR psi s (SS.bxor s y) * RR psi (SS.bxor (SS.bxor s P.x) y) (SS.bxor s P.x)) := by
    rw [core]; exact Finset.sum_comm
  rw [hcore]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← sum_bxor_reindex' s
      (fun t => ((chi P.z (SS.bxor s t) : ℝ) : ℂ)
        * (RR psi (SS.bxor t P.x) (SS.bxor s P.x) * RR psi s t))]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [bxor_cancel_left, bxor_right_comm]
  ring

/-! ## 7.  The duality (Parseval) step of the MacWilliams identity -/

theorem pauli_duality_C (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    ∑ Q : SS.PauliString n,
        (((chi P.x Q.z : ℝ) : ℂ) * ((chi P.z Q.x : ℝ) : ℂ))
          * ((Complex.normSq (trProj psi Q) : ℝ) : ℂ)
      = (2 : ℂ) ^ n * ((frob psi P : ℝ) : ℂ) := by
  have h1 : ∀ Q : SS.PauliString n, ((Complex.normSq (trProj psi Q) : ℝ) : ℂ)
      = melTr psi Q * star (melTr psi Q) := by
    intro Q; rw [normSq_trProj, normSq_cast]
  have h2 : ((frob psi P : ℝ) : ℂ)
      = ∑ a, ∑ b, mel (psi a) (psi b) P * star (mel (psi a) (psi b) P) := by
    rw [frob, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun b _ => by rw [normSq_innerC, normSq_cast])
  simp only [h1]
  rw [h2, lhs_eq_core, rhs_eq_core]

/-- **The duality step of the quantum MacWilliams identity.**  For every Pauli
`P`, the commutation-signed sum of `|Tr (Q Pi)|^2` over all `4^n` Paulis `Q`
equals `2^n * Tr (P Pi P^dagger Pi)`.  No hypothesis whatsoever is placed on the
family `psi`. -/
theorem pauli_duality (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    ∑ Q : SS.PauliString n,
        chi P.x Q.z * chi P.z Q.x * Complex.normSq (trProj psi Q)
      = 2 ^ n * frob psi P := by
  have e1 : ((∑ Q : SS.PauliString n,
        chi P.x Q.z * chi P.z Q.x * Complex.normSq (trProj psi Q) : ℝ) : ℂ)
      = ∑ Q : SS.PauliString n,
          (((chi P.x Q.z : ℝ) : ℂ) * ((chi P.z Q.x : ℝ) : ℂ))
            * ((Complex.normSq (trProj psi Q) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun Q _ => by push_cast; ring)
  have e2 : ((2 ^ n * frob psi P : ℝ) : ℂ) = (2 : ℂ) ^ n * ((frob psi P : ℝ) : ℂ) := by
    push_cast; ring
  apply Complex.ofReal_injective
  rw [e1, e2]
  exact pauli_duality_C psi P

/-! ## 8.  Paulis supported inside a set of qubits -/

/-- The support of a Pauli string: the qubits it acts on nontrivially. -/
def supp (P : SS.PauliString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => P.x i || P.z i)

lemma wt_eq_card_supp (P : SS.PauliString n) : P.wt = (supp P).card := rfl

lemma supp_subset_iff (S : Finset (Fin n)) (x z : SS.BitString n) :
    supp (⟨x, z⟩ : SS.PauliString n) ⊆ S ↔ (x ∈ cube S ∧ z ∈ cube S) := by
  classical
  constructor
  · intro h
    constructor <;> rw [mem_cube] <;> intro i hi
    · by_contra hx
      exact hi (h (Finset.mem_filter.mpr ⟨Finset.mem_univ i, by
        simp only [Bool.or_eq_true]
        exact Or.inl (by simpa using hx)⟩))
    · by_contra hz
      exact hi (h (Finset.mem_filter.mpr ⟨Finset.mem_univ i, by
        simp only [Bool.or_eq_true]
        exact Or.inr (by simpa using hz)⟩))
  · rintro ⟨hx, hz⟩ i hi
    rw [mem_cube] at hx hz
    by_contra hiS
    have h1 : x i = false := hx i hiS
    have h2 : z i = false := hz i hiS
    have hi2 : (x i || z i) = true := (Finset.mem_filter.mp hi).2
    rw [h1, h2] at hi2
    simp at hi2

/-- The Paulis supported inside `S` form a product of two sub-cubes. -/
lemma sum_pauli_cube {M : Type*} [AddCommMonoid M] (S : Finset (Fin n))
    (f : SS.PauliString n → M) :
    ∑ P ∈ Finset.univ.filter (fun P => supp P ⊆ S), f P
      = ∑ x ∈ cube S, ∑ z ∈ cube S, f ⟨x, z⟩ := by
  classical
  calc ∑ P ∈ Finset.univ.filter (fun P => supp P ⊆ S), f P
      = ∑ P : SS.PauliString n, if supp P ⊆ S then f P else 0 := Finset.sum_filter _ _
    _ = ∑ x : SS.BitString n, ∑ z : SS.BitString n,
          (if supp (⟨x, z⟩ : SS.PauliString n) ⊆ S then f ⟨x, z⟩ else 0) := sum_pauli _
    _ = ∑ x : SS.BitString n, ∑ z : SS.BitString n,
          (if x ∈ cube S then (if z ∈ cube S then f ⟨x, z⟩ else 0) else 0) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
        by_cases hx : x ∈ cube S
        · by_cases hz : z ∈ cube S
          · rw [if_pos ((supp_subset_iff S x z).mpr ⟨hx, hz⟩), if_pos hx, if_pos hz]
          · rw [if_neg (fun h => hz ((supp_subset_iff S x z).mp h).2), if_pos hx, if_neg hz]
        · rw [if_neg (fun h => hx ((supp_subset_iff S x z).mp h).1), if_neg hx]
    _ = ∑ x : SS.BitString n, (if x ∈ cube S then ∑ z ∈ cube S, f ⟨x, z⟩ else 0) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        by_cases hx : x ∈ cube S
        · simp only [if_pos hx]
          rw [Finset.sum_ite_mem, Finset.univ_inter]
        · simp only [if_neg hx, Finset.sum_const_zero]
    _ = ∑ x ∈ cube S, ∑ z ∈ cube S, f ⟨x, z⟩ := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The commutation signs of the Paulis supported inside `S`, summed. -/
lemma sum_sign_cube (S : Finset (Fin n)) (Q : SS.PauliString n) :
    ∑ P ∈ Finset.univ.filter (fun P => supp P ⊆ S), chi P.x Q.z * chi P.z Q.x
      = if (∀ i ∈ S, Q.x i = false ∧ Q.z i = false) then (4 : ℝ) ^ S.card else 0 := by
  classical
  rw [sum_pauli_cube]
  have hred : (∑ x ∈ cube S, ∑ z ∈ cube S,
      chi (⟨x, z⟩ : SS.PauliString n).x Q.z * chi (⟨x, z⟩ : SS.PauliString n).z Q.x)
      = (∑ x ∈ cube S, chi x Q.z) * (∑ z ∈ cube S, chi z Q.x) :=
    (Finset.sum_mul_sum (cube S) (cube S) (fun x => chi x Q.z) (fun z => chi z Q.x)).symm
  rw [hred, sum_chi_cube, sum_chi_cube]
  by_cases h : ∀ i ∈ S, Q.x i = false ∧ Q.z i = false
  · rw [if_pos h, if_pos (fun i hi => (h i hi).2), if_pos (fun i hi => (h i hi).1)]
    rw [← mul_pow]
    norm_num
  · rw [if_neg h]
    by_cases hz : ∀ i ∈ S, Q.z i = false
    · rw [if_pos hz, if_neg (fun hx => h (fun i hi => ⟨hx i hi, hz i hi⟩)), mul_zero]
    · rw [if_neg hz, zero_mul]

/-! ## 9.  The subset form of the MacWilliams identity -/

/-- **The MacWilliams identity in subset form.**  For every set `S` of qubits,
the total `B`-weight of the Paulis supported inside `S` is `4^{|S|}/2^n` times
the total `A`-weight of the Paulis acting trivially on `S`.  Again no hypothesis
is placed on `psi`. -/
theorem subset_duality (psi : Fin K → SS.State n ℂ) (S : Finset (Fin n)) :
    (2 : ℝ) ^ n * ∑ P ∈ Finset.univ.filter (fun P => supp P ⊆ S), frob psi P
      = (4 : ℝ) ^ S.card
          * ∑ Q ∈ Finset.univ.filter (fun Q : SS.PauliString n =>
                ∀ i ∈ S, Q.x i = false ∧ Q.z i = false),
              Complex.normSq (trProj psi Q) := by
  classical
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun P (_ : P ∈ Finset.univ.filter (fun P => supp P ⊆ S)) =>
      (pauli_duality psi P).symm)]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [← Finset.sum_mul, sum_sign_cube]
  by_cases h : ∀ i ∈ S, Q.x i = false ∧ Q.z i = false
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]

/-! ## 10.  The Knill--Laflamme input -/

/-- If the Knill--Laflamme condition holds for `P`, its `B`-weight and its
`A`-weight agree up to the factor `K`. -/
lemma frob_of_KL (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n)
    (h : SS.KLCondition psi P) :
    (K : ℝ) * frob psi P = Complex.normSq (trProj psi P) := by
  classical
  obtain ⟨c, hc⟩ := h
  have hfrob : frob psi P = (K : ℝ) * Complex.normSq c := by
    rw [frob]
    have hin : ∀ a : Fin K,
        (∑ b, Complex.normSq (SS.innerC (psi a) (SS.pauliAct P (psi b))))
          = Complex.normSq c := by
      intro a
      have hb : ∀ b : Fin K, Complex.normSq (SS.innerC (psi a) (SS.pauliAct P (psi b)))
          = if a = b then Complex.normSq c else 0 := by
        intro b
        rw [hc a b]
        by_cases h : a = b
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, Complex.normSq_zero]
      rw [Finset.sum_congr rfl (fun b _ => hb b),
        Finset.sum_ite_eq Finset.univ a (fun _ => Complex.normSq c),
        if_pos (Finset.mem_univ a)]
    rw [Finset.sum_congr rfl (fun a _ => hin a), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have htr : trProj psi P = (K : ℂ) * c := by
    rw [trProj]
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => by rw [hc a a, if_pos rfl])]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hfrob, htr, map_mul]
  have : Complex.normSq (K : ℂ) = (K : ℝ) * (K : ℝ) := by
    rw [show ((K : ℂ)) = (((K : ℝ) : ℂ)) by push_cast; ring, Complex.normSq_ofReal]
  rw [this]
  ring

/-! ## 11.  Fibering the enumerator over Pauli supports -/

/-- The `A`-weight carried by the Paulis whose support is exactly `T`. -/
def gsub (psi : Fin K → SS.State n ℂ) (T : Finset (Fin n)) : ℝ :=
  ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => supp P = T),
      Complex.normSq (trProj psi P)

/-- The unnormalised Shor--Laflamme coefficient
`K^2 * A_j = ∑_{wt P = j} |Tr (P Pi)|^2`. -/
def Aco (psi : Fin K → SS.State n ℂ) (j : ℕ) : ℝ :=
  ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => P.wt = j),
      Complex.normSq (trProj psi P)

lemma fiber_supp (psi : Fin K → SS.State n ℂ) (pred : Finset (Fin n) → Prop)
    [DecidablePred pred] :
    ∑ T ∈ Finset.univ.filter pred, gsub psi T
      = ∑ P ∈ Finset.univ.filter (fun P => pred (supp P)),
          Complex.normSq (trProj psi P) := by
  classical
  simp only [gsub]
  rw [Finset.sum_fiberwise_eq_sum_filter]
  refine Finset.sum_congr (Finset.filter_congr (fun P _ => ?_)) (fun _ _ => rfl)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma sum_gsub_card (psi : Fin K → SS.State n ℂ) (j : ℕ) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T.card = j), gsub psi T
      = Aco psi j :=
  fiber_supp psi (fun T => T.card = j)

lemma sum_gsub_subset (psi : Fin K → SS.State n ℂ) (S : Finset (Fin n)) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T ⊆ S), gsub psi T
      = ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => supp P ⊆ S),
          Complex.normSq (trProj psi P) :=
  fiber_supp psi (fun T => T ⊆ S)

lemma supp_compl_iff (S : Finset (Fin n)) (Q : SS.PauliString n) :
    supp Q ⊆ Sᶜ ↔ ∀ i ∈ S, Q.x i = false ∧ Q.z i = false := by
  classical
  constructor
  · intro h i hi
    by_contra hc
    have hmem : i ∈ supp Q := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩
      rcases Bool.eq_false_or_eq_true (Q.x i) with hx | hx
      · simp [hx]
      · rcases Bool.eq_false_or_eq_true (Q.z i) with hz | hz
        · simp [hz]
        · exact absurd ⟨hx, hz⟩ hc
    exact (Finset.mem_compl.mp (h hmem)) hi
  · intro h i hi
    refine Finset.mem_compl.mpr (fun hiS => ?_)
    obtain ⟨hx, hz⟩ := h i hiS
    have hb : (Q.x i || Q.z i) = true := (Finset.mem_filter.mp hi).2
    rw [hx, hz] at hb
    simp at hb

lemma sum_gsub_compl (psi : Fin K → SS.State n ℂ) (S : Finset (Fin n)) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T ⊆ Sᶜ), gsub psi T
      = ∑ Q ∈ Finset.univ.filter (fun Q : SS.PauliString n =>
            ∀ i ∈ S, Q.x i = false ∧ Q.z i = false),
          Complex.normSq (trProj psi Q) := by
  classical
  rw [fiber_supp psi (fun T => T ⊆ Sᶜ)]
  exact Finset.sum_congr (Finset.filter_congr (fun Q _ => supp_compl_iff S Q)) (fun _ _ => rfl)

/-! ## 12.  The MacWilliams identity for a code that detects everything on `S` -/

/-- **The MacWilliams identity, subset form, for a code.**  If the
Knill--Laflamme conditions hold for every Pauli supported inside `S`, then the
`A`-weight of the Paulis supported inside `S` and the `A`-weight of the Paulis
acting trivially on `S` determine each other. -/
theorem subset_macwilliams (psi : Fin K → SS.State n ℂ) (S : Finset (Fin n))
    (hKL : ∀ P : SS.PauliString n, supp P ⊆ S → SS.KLCondition psi P) :
    (2 : ℝ) ^ n * ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T ⊆ S), gsub psi T
      = (K : ℝ) * (4 : ℝ) ^ S.card
          * ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => T ⊆ Sᶜ), gsub psi T := by
  classical
  rw [sum_gsub_subset, sum_gsub_compl]
  have h1 : ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => supp P ⊆ S),
        Complex.normSq (trProj psi P)
      = (K : ℝ) * ∑ P ∈ Finset.univ.filter (fun P : SS.PauliString n => supp P ⊆ S),
          frob psi P := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun P hP =>
      (frob_of_KL psi P (hKL P (Finset.mem_filter.mp hP).2)).symm)
  rw [h1, mul_left_comm, subset_duality]
  ring

/-! ## 13.  Averaging the identity over all sets of qubits of a given size -/

lemma swap_count (Sset : Finset (Finset (Fin n)))
    (p : Finset (Fin n) → Finset (Fin n) → Prop) [DecidableRel p] (g : Finset (Fin n) → ℝ) :
    ∑ S ∈ Sset, ∑ T ∈ Finset.univ.filter (fun T => p S T), g T
      = ∑ T : Finset (Fin n), ((Sset.filter (fun S => p S T)).card : ℝ) * g T := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

lemma card_fiber6 (c : ℕ → ℝ) (g : Finset (Fin 6) → ℝ) :
    ∑ T : Finset (Fin 6), c T.card * g T
      = ∑ k ∈ Finset.range 7,
          c k * ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin 6) => T.card = k), g T := by
  classical
  have hmap : ∀ T ∈ (Finset.univ : Finset (Finset (Fin 6))), T.card ∈ Finset.range 7 := by
    intro T _
    rw [Finset.mem_range]
    have h : T.card ≤ 6 := by simpa using Finset.card_le_univ T
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun T => c T.card * g T)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_filter.mp hT).2])

/-! ## 14.  The six-qubit counting certificates -/

lemma cnt_sup0 : ∀ T : Finset (Fin 6),
    (((Finset.univ : Finset (Fin 6)).powersetCard 0).filter (fun S => T ⊆ S)).card
      = (if T.card = 0 then 1 else 0) := by decide

lemma cnt_dis0 : ∀ T : Finset (Fin 6),
    (((Finset.univ : Finset (Fin 6)).powersetCard 0).filter (fun S => T ⊆ Sᶜ)).card
      = 1 := by decide

lemma cnt_sup1 : ∀ T : Finset (Fin 6),
    (((Finset.univ : Finset (Fin 6)).powersetCard 1).filter (fun S => T ⊆ S)).card
      = (if T.card = 0 then 6 else if T.card = 1 then 1 else 0) := by decide

lemma cnt_dis1 : ∀ T : Finset (Fin 6),
    (((Finset.univ : Finset (Fin 6)).powersetCard 1).filter (fun S => T ⊆ Sᶜ)).card
      = 6 - T.card := by decide

lemma cnt_sup2 : ∀ T : Finset (Fin 6),
    (((Finset.univ : Finset (Fin 6)).powersetCard 2).filter (fun S => T ⊆ S)).card
      = (if T.card = 0 then 15 else if T.card = 1 then 5 else if T.card = 2 then 1 else 0) := by
  decide

lemma cnt_dis2 : ∀ T : Finset (Fin 6),
    (((Finset.univ : Finset (Fin 6)).powersetCard 2).filter (fun S => T ⊆ Sᶜ)).card
      = (if T.card = 0 then 15 else if T.card = 1 then 10 else if T.card = 2 then 6
          else if T.card = 3 then 3 else if T.card = 4 then 1 else 0) := by decide

/-! ## 15.  The averaged relation -/

/-- Averaging `subset_macwilliams` over all `m`-element sets of qubits turns it
into a linear relation among the Shor--Laflamme coefficients, with coefficients
given by the two counting functions `cf` (supersets) and `df` (disjointness). -/
theorem summed_relation (psi : Fin 2 → SS.State 6 ℂ) (hd3 : SS.HasDistance psi 3)
    (m : ℕ) (hm : m ≤ 2) (cf df : ℕ → ℕ)
    (hcf : ∀ T : Finset (Fin 6),
      (((Finset.univ : Finset (Fin 6)).powersetCard m).filter (fun S => T ⊆ S)).card = cf T.card)
    (hdf : ∀ T : Finset (Fin 6),
      (((Finset.univ : Finset (Fin 6)).powersetCard m).filter (fun S => T ⊆ Sᶜ)).card
        = df T.card) :
    (2 : ℝ) ^ 6 * ∑ k ∈ Finset.range 7, (cf k : ℝ) * Aco psi k
      = 2 * 4 ^ m * ∑ k ∈ Finset.range 7, (df k : ℝ) * Aco psi k := by
  classical
  have hKL : ∀ S : Finset (Fin 6), S.card = m →
      ∀ P : SS.PauliString 6, supp P ⊆ S → SS.KLCondition psi P := by
    intro S hS P hP
    refine hd3 P ?_
    have hw : P.wt = (supp P).card := rfl
    have : (supp P).card ≤ 2 := le_trans (le_trans (Finset.card_le_card hP) (le_of_eq hS)) hm
    omega
  have hstep : ∀ S ∈ (Finset.univ : Finset (Fin 6)).powersetCard m,
      (2 : ℝ) ^ 6 * ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin 6) => T ⊆ S), gsub psi T
        = 2 * 4 ^ m
            * ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin 6) => T ⊆ Sᶜ), gsub psi T := by
    intro S hS
    have hcard : S.card = m := (Finset.mem_powersetCard.mp hS).2
    have h := subset_macwilliams psi S (hKL S hcard)
    rw [hcard] at h
    push_cast at h
    exact h
  have hsum := Finset.sum_congr rfl hstep
  rw [← Finset.mul_sum, ← Finset.mul_sum, swap_count, swap_count] at hsum
  simp only [hcf, hdf] at hsum
  rw [card_fiber6 (fun k => (cf k : ℝ)) (gsub psi),
    card_fiber6 (fun k => (df k : ℝ)) (gsub psi)] at hsum
  simp only [sum_gsub_card] at hsum
  exact hsum

/-! ## 16.  The MacWilliams normal form of a `((6, 2, 3))` code -/

/-- **The MacWilliams normal form.**  For any two-dimensional six-qubit code of
distance three whose zeroth Shor--Laflamme coefficient is the normal one
(`A_0 = 1`, i.e. `Tr Pi = 2`), the top three coefficients are determined by the
bottom three.  Dividing through by `K^2 = 4` this is exactly

    A_4 = 15 - 4 A_2 - 3 A_3,
    A_5 = 12 + 3 A_1 + 4 A_2 + 3 A_3,
    A_6 = 4  - 4 A_1 -   A_2 -   A_3.
-/
theorem macwilliams_six (psi : Fin 2 → SS.State 6 ℂ) (hd3 : SS.HasDistance psi 3)
    (hA0 : Aco psi 0 = 4) :
    Aco psi 4 = 60 - 4 * Aco psi 2 - 3 * Aco psi 3
      ∧ Aco psi 5 = 48 + 3 * Aco psi 1 + 4 * Aco psi 2 + 3 * Aco psi 3
      ∧ Aco psi 6 = 16 - 4 * Aco psi 1 - Aco psi 2 - Aco psi 3 := by
  have h0 := summed_relation psi hd3 0 (by norm_num)
      (fun k => if k = 0 then 1 else 0) (fun _ => 1) cnt_sup0 cnt_dis0
  have h1 := summed_relation psi hd3 1 (by norm_num)
      (fun k => if k = 0 then 6 else if k = 1 then 1 else 0) (fun k => 6 - k)
      cnt_sup1 cnt_dis1
  have h2 := summed_relation psi hd3 2 (by norm_num)
      (fun k => if k = 0 then 15 else if k = 1 then 5 else if k = 2 then 1 else 0)
      (fun k => if k = 0 then 15 else if k = 1 then 10 else if k = 2 then 6
          else if k = 3 then 3 else if k = 4 then 1 else 0) cnt_sup2 cnt_dis2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h0 h1 h2
  norm_num at h0 h1 h2
  refine ⟨by linarith, by linarith, by linarith⟩

end

end MacWilliams
end SS

/-! ## 17.  Closing the conditional gap of `Orbit36Enum.unique_enumerator` -/

namespace SixQubit
namespace Orbit36MacWilliams

open SixQubit.Orbit36
open SS.MacWilliams

noncomputable section

/-- The projector trace of `SixQubit.Orbit36Phase` is the `trProj` of the
two-element family `![c, d]`. -/
lemma trProj_pair (c d : SS.BitString 6 -> ℂ) (P : SS.PauliString 6) :
    SS.MacWilliams.trProj ![c, d] P = SixQubit.Orbit36Phase.projTrace c d P := by
  rw [SS.MacWilliams.trProj, SixQubit.Orbit36Phase.projTrace, Fin.sum_univ_two]
  rfl

/-- The unnormalised coefficient `Aco` of `![c, d]` is four times the chapter's
`AEnum`, because there `K^2 = 4`. -/
lemma Aco_pair (c d : SS.BitString 6 -> ℂ) (j : ℕ) :
    SS.MacWilliams.Aco ![c, d] j = 4 * SixQubit.Orbit36Phase.AEnum c d j := by
  classical
  rw [SixQubit.Orbit36Phase.AEnum, show ∀ X : ℝ, 4 * (X / 4) = X from fun X => by ring]
  rw [SS.MacWilliams.Aco, Finset.sum_filter, SS.MacWilliams.sum_pauli,
    SixQubit.Orbit36Phase.paulisOfWeight, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
  rw [trProj_pair]

/-- Every exact orbit-36 solution really is a distance-three code: it is
equivalent to the canonical representative, which is one. -/
theorem hasDistance_of_orbit36 (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5))
            (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))
    (ho0 : offSum c d ex1 w0 = 0)
    (ho1 : offSum c d ex1 w2 = 0)
    (ho2 : offSum c d ex1 w3 = 0)
    (ho3 : offSum c d ex1 w4 = 0)
    (ho4 : offSum c d ex2 w0 = 0)
    (ho5 : offSum c d ex2 w1 = 0)
    (ho6 : offSum c d ex2 w3 = 0)
    (ho7 : offSum c d ex2 w4 = 0)
    (ho8 : offSum c d ex3 w0 = 0)
    (ho9 : offSum c d ex3 w1 = 0)
    (ho10 : offSum c d ex3 w2 = 0)
    (ho11 : offSum c d ex3 w4 = 0)
    (ho12 : offSum c d ex4 w0 = 0)
    (ho13 : offSum c d ex4 w1 = 0)
    (ho14 : offSum c d ex4 w2 = 0)
    (ho15 : offSum c d ex4 w3 = 0)
    (ho16 : offSum c d ex15 w0 = 0)
    (ho17 : offSum c d ex25 w0 = 0)
    (ho18 : offSum c d ex35 w0 = 0)
    (ho19 : offSum c d ex45 w0 = 0)
    (ho20 : offSum c d ex56 w0 = 0)
    (ho21 : offSum c d SixQubit.Orbit36Enum.ex16 w0 = 0) :
    SS.HasDistance ![c, d] 3 :=
  (SixQubit.CodeEquiv.hasDistance_iff_of_equivalent
      (SixQubit.Orbit36Class.orbit36_theorem c d hc hd hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20 ho21).2.2).mpr
    SixQubit.Orbit36Code.canonical_is_code

/-- **The missing MacWilliams step of the chapter.**  For an arbitrary exact
orbit-36 solution the three hypotheses `hmw4`, `hmw5`, `hmw6` of
`SixQubit.Orbit36Enum.unique_enumerator` are theorems. -/
theorem macwilliams_normal_form (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5))
            (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))
    (ho0 : offSum c d ex1 w0 = 0)
    (ho1 : offSum c d ex1 w2 = 0)
    (ho2 : offSum c d ex1 w3 = 0)
    (ho3 : offSum c d ex1 w4 = 0)
    (ho4 : offSum c d ex2 w0 = 0)
    (ho5 : offSum c d ex2 w1 = 0)
    (ho6 : offSum c d ex2 w3 = 0)
    (ho7 : offSum c d ex2 w4 = 0)
    (ho8 : offSum c d ex3 w0 = 0)
    (ho9 : offSum c d ex3 w1 = 0)
    (ho10 : offSum c d ex3 w2 = 0)
    (ho11 : offSum c d ex3 w4 = 0)
    (ho12 : offSum c d ex4 w0 = 0)
    (ho13 : offSum c d ex4 w1 = 0)
    (ho14 : offSum c d ex4 w2 = 0)
    (ho15 : offSum c d ex4 w3 = 0)
    (ho16 : offSum c d ex15 w0 = 0)
    (ho17 : offSum c d ex25 w0 = 0)
    (ho18 : offSum c d ex35 w0 = 0)
    (ho19 : offSum c d ex45 w0 = 0)
    (ho20 : offSum c d ex56 w0 = 0)
    (ho21 : offSum c d SixQubit.Orbit36Enum.ex16 w0 = 0) :
    SixQubit.Orbit36Phase.AEnum c d 4
        = 15 - 4 * SixQubit.Orbit36Phase.AEnum c d 2
            - 3 * SixQubit.Orbit36Phase.AEnum c d 3
      ∧ SixQubit.Orbit36Phase.AEnum c d 5
        = 12 + 3 * SixQubit.Orbit36Phase.AEnum c d 1
            + 4 * SixQubit.Orbit36Phase.AEnum c d 2
            + 3 * SixQubit.Orbit36Phase.AEnum c d 3
      ∧ SixQubit.Orbit36Phase.AEnum c d 6
        = 4 - 4 * SixQubit.Orbit36Phase.AEnum c d 1
            - SixQubit.Orbit36Phase.AEnum c d 2
            - SixQubit.Orbit36Phase.AEnum c d 3 := by
  have hdist : SS.HasDistance ![c, d] 3 :=
    hasDistance_of_orbit36 c d hc hd hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20 ho21
  have hA0 : SixQubit.Orbit36Phase.AEnum c d 0 = 1 :=
    SixQubit.Orbit36Enum.A0_value c d hc hd hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20
  have h0 : SS.MacWilliams.Aco ![c, d] 0 = 4 := by
    rw [Aco_pair, hA0]; norm_num
  obtain ⟨h4, h5, h6⟩ := SS.MacWilliams.macwilliams_six ![c, d] hdist h0
  simp only [Aco_pair] at h4 h5 h6
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **The unique Shor--Laflamme weight enumerator on orbit 36, unconditionally.**
Same statement as `SixQubit.Orbit36Enum.unique_enumerator`, but with the three
MacWilliams hypotheses discharged and the three top coefficients read off the
enumerator itself. -/
theorem orbit36_enumerator (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ s, s ∉ S0 → c s = 0) (hd : ∀ s, s ∉ S1 → d s = 0)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5))
            (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5))
            (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)))
    (ho0 : offSum c d ex1 w0 = 0)
    (ho1 : offSum c d ex1 w2 = 0)
    (ho2 : offSum c d ex1 w3 = 0)
    (ho3 : offSum c d ex1 w4 = 0)
    (ho4 : offSum c d ex2 w0 = 0)
    (ho5 : offSum c d ex2 w1 = 0)
    (ho6 : offSum c d ex2 w3 = 0)
    (ho7 : offSum c d ex2 w4 = 0)
    (ho8 : offSum c d ex3 w0 = 0)
    (ho9 : offSum c d ex3 w1 = 0)
    (ho10 : offSum c d ex3 w2 = 0)
    (ho11 : offSum c d ex3 w4 = 0)
    (ho12 : offSum c d ex4 w0 = 0)
    (ho13 : offSum c d ex4 w1 = 0)
    (ho14 : offSum c d ex4 w2 = 0)
    (ho15 : offSum c d ex4 w3 = 0)
    (ho16 : offSum c d ex15 w0 = 0)
    (ho17 : offSum c d ex25 w0 = 0)
    (ho18 : offSum c d ex35 w0 = 0)
    (ho19 : offSum c d ex45 w0 = 0)
    (ho20 : offSum c d ex56 w0 = 0)
    (ho21 : offSum c d SixQubit.Orbit36Enum.ex16 w0 = 0) :
    SixQubit.Orbit36Phase.AEnum c d 0 = 1
      ∧ SixQubit.Orbit36Phase.AEnum c d 1 = 0
      ∧ SixQubit.Orbit36Phase.AEnum c d 2 = 21/25
      ∧ SixQubit.Orbit36Phase.AEnum c d 3 = 0
      ∧ SixQubit.Orbit36Phase.AEnum c d 4 = 291/25
      ∧ SixQubit.Orbit36Phase.AEnum c d 5 = 384/25
      ∧ SixQubit.Orbit36Phase.AEnum c d 6 = 79/25 := by
  obtain ⟨hmw4, hmw5, hmw6⟩ :=
    macwilliams_normal_form c d hc hd hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20 ho21
  exact SixQubit.Orbit36Enum.unique_enumerator c d hc hd hm ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 ho8 ho9 ho10 ho11 ho12 ho13 ho14 ho15 ho16 ho17 ho18 ho19 ho20 ho21
    (SixQubit.Orbit36Phase.AEnum c d 4) (SixQubit.Orbit36Phase.AEnum c d 5)
    (SixQubit.Orbit36Phase.AEnum c d 6) hmw4 hmw5 hmw6

end

end Orbit36MacWilliams
end SixQubit
