import Mathlib
import SS.HilbertKL
import SixQubit.MacWilliams
import SixQubit.Shadow

/-!
# The twisted shadow coefficients

`SixQubit/Shadow.lean` proves that the alternating Pauli sum is nonnegative.
Orbit 21 needs more: its Farkas certificate is a positive combination of the
*complete* shadow coefficients

    s_E = (1/32) sum_F (-1)^{wt F} (-1)^{<E,F>} a_F,

one for each of twenty-two labels, and `alt_sum_nonneg` is only the `E = I`
instance.  Substituting `E psi` for `psi` does not recover the others: that
changes `a_F` by a sign that cancels against the pairing, leaving the same
untwisted sum.

The generalization is exact, though, and costs nothing structurally.  The extra
sign factors the same way the weight sign does,

    (-1)^{<E,F>} = chi(F.x, E.z) * chi(F.z, E.x),

so the two combine into

    (-1)^{wt F} (-1)^{<E,F>}
      = chi(F.x, ones + E.z) * chi(F.z, complement F.x + E.x),

which is the untwisted factorization with `ones` replaced by `ones + E.z` and
the complement shifted by `E.x`.  Doing the `Z`-sum first collapses it exactly
as before, and the surviving index is again a complement -- of `s + E.x` rather
than of `s`.  What comes out is

    sum_F (-1)^{wt F} (-1)^{<E,F>} |Tr(F Pi)|^2
      = 2^n sum_{a,b} | sum_u (-1)^{|u.(ones+E.z)|} psi_a(u) psi_b(compl(u+E.x)) |^2,

again a sum of squared norms.  Setting `E.x = E.z = 0` recovers
`Shadow.alt_sum_eq_core`.

The identity was checked numerically over several `E` and several random
non-code pairs before any of this was written, which is what confirms it is
algebraic rather than a consequence of the code property.
-/

namespace SS.ShadowTwisted

open SS.MacWilliams SS.Shadow

variable {n K : ℕ}

/-! ## The twisted sign -/

/-- `(-1)^{<E,F>}`, the Pauli commutation pairing sign. -/
def pairSign (E F : SS.PauliString n) : ℝ := chi F.x E.z * chi F.z E.x

/-- `(-1)^{|u . (ones + ez)|}`: the parity weight, twisted by the `Z`-part. -/
def psignT (ez u : SS.BitString n) : ℝ := chi u (SS.bxor (ones n) ez)

lemma psignT_bxor (ez u v : SS.BitString n) :
    psignT ez (SS.bxor u v) = psignT ez u * psignT ez v :=
  chi_bxor_left u v _

@[simp] lemma psignT_star (ez u : SS.BitString n) :
    star ((psignT ez u : ℝ) : ℂ) = ((psignT ez u : ℝ) : ℂ) := by
  simp

/-- The two signs combine into one factorization of the same shape as the
untwisted one. -/
lemma altsignT_factor (E P : SS.PauliString n) :
    ((-1 : ℝ)) ^ P.wt * pairSign E P
      = chi P.x (SS.bxor (ones n) E.z)
        * chi P.z (SS.bxor (SS.complement P.x) E.x) := by
  simp only [altsign_factor, pairSign, chi_bxor_right]
  ring

/-! ## The twisted pairing and core -/

/-- The bilinear pairing whose squared norms make the twisted sum manifestly
nonnegative. -/
noncomputable def TfT (psi : Fin K → SS.State n ℂ) (ex ez : SS.BitString n)
    (a b : Fin K) : ℂ :=
  ∑ u, ((psignT ez u : ℝ) : ℂ) * psi a u * psi b (SS.complement (SS.bxor u ex))

/-- The quantity both computations reduce to. -/
noncomputable def coreT (psi : Fin K → SS.State n ℂ) (ex ez : SS.BitString n) : ℂ :=
  ∑ u, ∑ v, ((psignT ez u : ℝ) : ℂ) * ((psignT ez v : ℝ) : ℂ)
      * RR psi u v
      * RR psi (SS.complement (SS.bxor u ex)) (SS.complement (SS.bxor v ex))

lemma star_TfT (psi : Fin K → SS.State n ℂ) (ex ez : SS.BitString n) (a b : Fin K) :
    star (TfT psi ex ez a b)
      = ∑ v, ((psignT ez v : ℝ) : ℂ) * star (psi a v)
          * star (psi b (SS.complement (SS.bxor v ex))) := by
  unfold TfT
  rw [star_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  simp only [star_mul', psignT_star]

lemma normSq_TfT_expand (psi : Fin K → SS.State n ℂ) (ex ez : SS.BitString n)
    (a b : Fin K) :
    ((Complex.normSq (TfT psi ex ez a b) : ℝ) : ℂ)
      = ∑ u, ∑ v,
          (((psignT ez u : ℝ) : ℂ) * psi a u * psi b (SS.complement (SS.bxor u ex)))
          * (((psignT ez v : ℝ) : ℂ) * star (psi a v)
              * star (psi b (SS.complement (SS.bxor v ex)))) := by
  have h : ((Complex.normSq (TfT psi ex ez a b) : ℝ) : ℂ)
      = TfT psi ex ez a b * star (TfT psi ex ez a b) := by
    rw [Complex.star_def]
    exact (Complex.mul_conj _).symm
  rw [h, star_TfT]
  conv_lhs => rw [TfT]
  exact Finset.sum_mul_sum _ _ _ _

theorem coreT_eq_sum_normSq (psi : Fin K → SS.State n ℂ) (ex ez : SS.BitString n) :
    coreT psi ex ez
      = ∑ a, ∑ b, ((Complex.normSq (TfT psi ex ez a b) : ℝ) : ℂ) := by
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) =>
      normSq_TfT_expand psi ex ez a b))]
  rw [sum4_comm (fun a b u v =>
    (((psignT ez u : ℝ) : ℂ) * psi a u * psi b (SS.complement (SS.bxor u ex)))
      * (((psignT ez v : ℝ) : ℂ) * star (psi a v)
          * star (psi b (SS.complement (SS.bxor v ex)))))]
  unfold coreT RR
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
  have h2 : (∑ a, psi a u * star (psi a v))
        * (∑ b, psi b (SS.complement (SS.bxor u ex))
            * star (psi b (SS.complement (SS.bxor v ex))))
      = ∑ a, ∑ b, (psi a u * star (psi a v))
          * (psi b (SS.complement (SS.bxor u ex))
              * star (psi b (SS.complement (SS.bxor v ex)))) :=
    Finset.sum_mul_sum _ _ _ _
  rw [mul_assoc (((psignT ez u : ℝ) : ℂ) * ((psignT ez v : ℝ) : ℂ)), h2,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-! ## Two shifted bitstring identities

The untwisted collapse leaves `t = s + xbar`; here it leaves
`t = s + (xbar + ex)`, and these say what that index is. -/

lemma bxor_shift_left (s x ex : SS.BitString n) :
    SS.bxor (SS.bxor s (SS.bxor (SS.complement x) ex)) x
      = SS.complement (SS.bxor s ex) := by
  funext i
  have : ∀ p q r : Bool, xor (xor p (xor (!q) r)) q = !(xor p r) := by decide
  simpa only [SS.bxor_apply, SS.complement] using this (s i) (x i) (ex i)

lemma bxor_shift_right (s x ex : SS.BitString n) :
    SS.bxor s (SS.bxor (SS.complement x) ex)
      = SS.complement (SS.bxor (SS.bxor s x) ex) := by
  funext i
  have : ∀ p q r : Bool, xor p (xor (!q) r) = !(xor (xor p q) r) := by decide
  simpa only [SS.bxor_apply, SS.complement] using this (s i) (x i) (ex i)

/-! ## The `Z`-sum, collapsed -/

lemma zT_sum_collapse (psi : Fin K → SS.State n ℂ) (x ex : SS.BitString n) :
    ∑ z, ((chi z (SS.bxor (SS.complement x) ex) : ℝ) : ℂ)
        * ((Complex.normSq (melTr psi ⟨x, z⟩) : ℝ) : ℂ)
      = (2 : ℂ) ^ n * ∑ s, RR psi s (SS.bxor s x)
          * RR psi (SS.complement (SS.bxor s ex))
              (SS.complement (SS.bxor (SS.bxor s x) ex)) := by
  classical
  have step1 : ∀ z : SS.BitString n,
      ((chi z (SS.bxor (SS.complement x) ex) : ℝ) : ℂ)
          * ((Complex.normSq (melTr psi ⟨x, z⟩) : ℝ) : ℂ)
        = ∑ s, ∑ t,
            ((chi z (SS.bxor (SS.bxor (SS.complement x) ex) (SS.bxor s t)) : ℝ) : ℂ)
              * (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t) := by
    intro z
    rw [normSq_melTr_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    simp only [chi_bxor_right]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => step1 z), Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.sum_comm]
  have hz : ∀ t : SS.BitString n,
      ∑ z, ((chi z (SS.bxor (SS.bxor (SS.complement x) ex) (SS.bxor s t)) : ℝ) : ℂ)
            * (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t)
        = (if t = SS.bxor s (SS.bxor (SS.complement x) ex)
           then (2 : ℂ) ^ n * (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t)
           else 0) := by
    intro t
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_chi_univ]
    by_cases h : t = SS.bxor s (SS.bxor (SS.complement x) ex)
    · rw [if_pos ((bxor_triple_zero_iff _ _ _).mpr h), if_pos h]
      push_cast
      ring
    · rw [if_neg (fun hc => h ((bxor_triple_zero_iff _ _ _).mp hc)), if_neg h]
      simp
  rw [Finset.sum_congr rfl (fun t (_ : t ∈ Finset.univ) => hz t),
    Finset.sum_ite_eq' Finset.univ (SS.bxor s (SS.bxor (SS.complement x) ex))
      (fun t => (2 : ℂ) ^ n * (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t)),
    if_pos (Finset.mem_univ _), bxor_shift_left, bxor_shift_right]

/-! ## Assembly -/

theorem altT_sum_eq_coreT (psi : Fin K → SS.State n ℂ) (E : SS.PauliString n) :
    ∑ P : SS.PauliString n,
        ((((-1 : ℝ)) ^ P.wt * pairSign E P
            * Complex.normSq (trProj psi P) : ℝ) : ℂ)
      = (2 : ℂ) ^ n * coreT psi E.x E.z := by
  classical
  have hterm : ∀ x z : SS.BitString n,
      (((((-1 : ℝ)) ^ (⟨x, z⟩ : SS.PauliString n).wt
          * pairSign E ⟨x, z⟩
          * Complex.normSq (trProj psi ⟨x, z⟩)) : ℝ) : ℂ)
        = ((chi x (SS.bxor (ones n) E.z) : ℝ) : ℂ)
            * (((chi z (SS.bxor (SS.complement x) E.x) : ℝ) : ℂ)
              * ((Complex.normSq (melTr psi ⟨x, z⟩) : ℝ) : ℂ)) := by
    intro x z
    rw [show ((-1 : ℝ)) ^ (⟨x, z⟩ : SS.PauliString n).wt * pairSign E ⟨x, z⟩
        = chi x (SS.bxor (ones n) E.z) * chi z (SS.bxor (SS.complement x) E.x) from
      altsignT_factor E ⟨x, z⟩, normSq_trProj]
    push_cast
    ring
  rw [sum_pauli, Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun z (_ : z ∈ Finset.univ) => hterm x z))]
  have hx : ∀ x : SS.BitString n,
      ∑ z, ((chi x (SS.bxor (ones n) E.z) : ℝ) : ℂ)
          * (((chi z (SS.bxor (SS.complement x) E.x) : ℝ) : ℂ)
            * ((Complex.normSq (melTr psi ⟨x, z⟩) : ℝ) : ℂ))
        = ((chi x (SS.bxor (ones n) E.z) : ℝ) : ℂ) * ((2 : ℂ) ^ n
            * ∑ s, RR psi s (SS.bxor s x)
                * RR psi (SS.complement (SS.bxor s E.x))
                    (SS.complement (SS.bxor (SS.bxor s x) E.x))) := by
    intro x
    rw [← Finset.mul_sum, zT_sum_collapse psi x E.x]
  have hy : ∀ x : SS.BitString n,
      ((chi x (SS.bxor (ones n) E.z) : ℝ) : ℂ) * ((2 : ℂ) ^ n
          * ∑ s, RR psi s (SS.bxor s x)
              * RR psi (SS.complement (SS.bxor s E.x))
                  (SS.complement (SS.bxor (SS.bxor s x) E.x)))
        = (2 : ℂ) ^ n * ∑ s, ((chi x (SS.bxor (ones n) E.z) : ℝ) : ℂ)
            * (RR psi s (SS.bxor s x)
              * RR psi (SS.complement (SS.bxor s E.x))
                  (SS.complement (SS.bxor (SS.bxor s x) E.x))) := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun (s : SS.BitString n) _ => by ring)
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => (hx x).trans (hy x)),
    ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm, coreT]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [← sum_bxor_reindex' (M := ℂ) s (fun x =>
    ((chi x (SS.bxor (ones n) E.z) : ℝ) : ℂ)
      * (RR psi s (SS.bxor s x)
        * RR psi (SS.complement (SS.bxor s E.x))
            (SS.complement (SS.bxor (SS.bxor s x) E.x))))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [bxor_cancel, show chi (SS.bxor s v) (SS.bxor (ones n) E.z)
      = psignT E.z s * psignT E.z v from psignT_bxor E.z s v]
  push_cast
  ring

/-- **Twisted shadow positivity.**

Every complete shadow coefficient is nonnegative, for every label `E`, every
block length and every number of logical states.  `Shadow.alt_sum_nonneg` is the
`E = I` instance. -/
theorem altT_sum_nonneg (psi : Fin K → SS.State n ℂ) (E : SS.PauliString n) :
    0 ≤ ∑ P : SS.PauliString n,
        ((-1 : ℝ)) ^ P.wt * pairSign E P * Complex.normSq (trProj psi P) := by
  have h := altT_sum_eq_coreT psi E
  rw [coreT_eq_sum_normSq] at h
  have hcast : ((∑ P : SS.PauliString n,
        ((-1 : ℝ)) ^ P.wt * pairSign E P
          * Complex.normSq (trProj psi P) : ℝ) : ℂ)
      = (((2 : ℝ) ^ n
          * ∑ a, ∑ b, Complex.normSq (TfT psi E.x E.z a b) : ℝ) : ℂ) := by
    push_cast
    push_cast at h
    exact h
  rw [Complex.ofReal_inj.mp hcast]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun a _ =>
      Finset.sum_nonneg (fun b _ => Complex.normSq_nonneg _)))

end SS.ShadowTwisted
