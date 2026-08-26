import Mathlib
import SixQubit.MacWilliams
import SixQubit.Orbit21Coef
import SixQubit.Orbit21Cert
import SixQubit.Orbit21Walsh
import SixQubit.Orbit21Bridge
import SixQubit.Realize

/-!
# Orbit 21: the support-level Walsh certificate

The first orbit-21 coefficient certificate tried to kill every Pauli whose
`X`-mask did not preserve the whole residue fibre.  That statement is false:
the logical words may use proper subsets of their fibres.  The certificate
nevertheless has a stronger, correct interpretation.  After expanding a
squared projector trace, the coefficient is tested only against
autocorrelations of pairs of words in the two prescribed fibres.  Its Walsh
transform vanishes on every such pair.

This module proves that statement directly.  The only finite fact is
`walsh_zero_on_pairs`, checked by the kernel on the 64 possible masks.  The
rest is an algebraic expansion of `normSq (trProj ...)`; no numerical solver or
external checker is part of the proof.
-/

namespace SixQubit.Orbit21Residual

open SS.MacWilliams SixQubit.Realize

/-- The integral Walsh sign attached to two bit strings. -/
def eps (z u : SS.BitString 6) : Int :=
  if SS.bdot z u then -1 else 1

/-- The Walsh transform of the integral certificate coefficient in its
`Z`-mask, at fixed `X`-mask. -/
def walsh (x u : SS.BitString 6) : Int :=
  ∑ z : SS.BitString 6,
    Orbit21Coef.coef (num x) (num z) * eps z u

/-- `s` and `s+x` belong to the same one of orbit 21's two fibres. -/
def sameFiber (x s : SS.BitString 6) : Prop :=
  (SS.weight Orbit21Cert.av s = 0 ∧
      SS.weight Orbit21Cert.av (SS.bxor s x) = 0) ∨
  (SS.weight Orbit21Cert.av s = 2 ∧
      SS.weight Orbit21Cert.av (SS.bxor s x) = 2)

instance (x : SS.BitString 6) : DecidablePred (sameFiber x) :=
  fun _ => by unfold sameFiber; infer_instance

set_option maxRecDepth 40000 in
/-- Encoding a bitstring pair preserves the fibre-pair predicate. -/
lemma sameFiber_num (x s : SS.BitString 6) (h : sameFiber x s) :
    SixQubit.Orbit21Walsh.sameFiber (num x) (num s) = true := by
  revert x s h
  decide

/-- Six-bit masks and six-bit strings are equivalent. -/
def maskEquiv : SS.BitString 6 ≃ Fin 64 where
  toFun s := ⟨num s, num_lt s⟩
  invFun m := nbit m
  left_inv := nbit_num
  right_inv := by decide

set_option maxRecDepth 40000 in
/-- The two definitions of the Walsh sign agree under mask encoding. -/
lemma eps_num (z u : SS.BitString 6) :
    eps z u = Orbit21Coef.sgn (Orbit21Coef.pc (num z &&& num u)) := by
  revert z u
  decide

/-- The bitstring Walsh sum is the compact Nat-mask sum checked in
`Orbit21Walsh`. -/
lemma walsh_eq_fourier (x u : SS.BitString 6) :
    walsh x u = SixQubit.Orbit21Walsh.fourierCoef (num x) (num u) := by
  unfold walsh SixQubit.Orbit21Walsh.fourierCoef
  rw [← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv maskEquiv
    (fun z => Orbit21Coef.coef (num x) (num z) * eps z u)
    (fun z : Fin 64 => Orbit21Coef.coef (num x) z *
      Orbit21Coef.sgn (Orbit21Coef.pc (z &&& num u)))
    (fun z => by
      change Orbit21Coef.coef (num x) (num z) * eps z u =
        Orbit21Coef.coef (num x) (num z) *
          Orbit21Coef.sgn (Orbit21Coef.pc (num z &&& num u))
      rw [eps_num])

/-- Convenient bitstring form of the 512-entry finite certificate. -/
theorem walsh_zero_on_pairs (x s t : SS.BitString 6)
    (hs : sameFiber x s) (ht : sameFiber x t) :
    walsh x (SS.bxor s t) = 0 := by
  rw [walsh_eq_fourier]
  apply SixQubit.Orbit21Walsh.fourierCoef_zero (num x) (num_lt x)
    (num (SS.bxor s t)) (num_lt _)
  have ha := SixQubit.Orbit21Walsh.active_of_sameFiber (num x) (num_lt x)
    (num s) (num_lt s) (num t) (num_lt t)
    (sameFiber_num x s hs) (sameFiber_num x t ht)
  rw [SixQubit.Orbit21Bridge.num_bxor]
  exact ha

/-- The integral sign is exactly the real Walsh character. -/
lemma eps_cast (z u : SS.BitString 6) :
    ((eps z u : Int) : ℂ) = ((chi z u : ℝ) : ℂ) := by
  by_cases h : SS.bdot z u = true
  · have hsign := signC_bdot z u (1 : ℂ)
    rw [h, SS.signC_true] at hsign
    simp only [eps, h, if_pos]
    norm_num at hsign ⊢
    exact hsign
  · have hb : SS.bdot z u = false := Bool.eq_false_of_not_eq_true h
    have hsign := signC_bdot z u (1 : ℂ)
    rw [hb, SS.signC_false] at hsign
    simp only [eps, hb, Bool.false_eq_true, if_false]
    norm_num at hsign ⊢
    exact hsign

/-- If a pair does not stay inside one logical fibre, its correlation matrix
entry vanishes. -/
lemma RR_zero_of_not_sameFiber (psi : Fin 2 → SS.State 6 ℂ)
    (h0 : ∀ s, SS.weight Orbit21Cert.av s ≠ 0 → psi 0 s = 0)
    (h1 : ∀ s, SS.weight Orbit21Cert.av s ≠ 2 → psi 1 s = 0)
    (x s : SS.BitString 6) (h : ¬ sameFiber x s) :
    RR psi s (SS.bxor s x) = 0 := by
  unfold RR
  rw [Fin.sum_univ_two]
  have hz0 : psi 0 s * star (psi 0 (SS.bxor s x)) = 0 := by
    by_cases hs : SS.weight Orbit21Cert.av s = 0
    · have ht : SS.weight Orbit21Cert.av (SS.bxor s x) ≠ 0 := by
        intro ht
        exact h (Or.inl ⟨hs, ht⟩)
      rw [h0 (SS.bxor s x) ht, star_zero, mul_zero]
    · rw [h0 s hs, zero_mul]
  have hz1 : psi 1 s * star (psi 1 (SS.bxor s x)) = 0 := by
    by_cases hs : SS.weight Orbit21Cert.av s = 2
    · have ht : SS.weight Orbit21Cert.av (SS.bxor s x) ≠ 2 := by
        intro ht
        exact h (Or.inr ⟨hs, ht⟩)
      rw [h1 (SS.bxor s x) ht, star_zero, mul_zero]
    · rw [h1 s hs, zero_mul]
  rw [hz0, hz1, add_zero]

/-- The reversed correlation entry vanishes under the same condition. -/
lemma RR_reverse_zero_of_not_sameFiber (psi : Fin 2 → SS.State 6 ℂ)
    (h0 : ∀ s, SS.weight Orbit21Cert.av s ≠ 0 → psi 0 s = 0)
    (h1 : ∀ s, SS.weight Orbit21Cert.av s ≠ 2 → psi 1 s = 0)
    (x s : SS.BitString 6) (h : ¬ sameFiber x s) :
    RR psi (SS.bxor s x) s = 0 := by
  rw [← star_RR]
  rw [RR_zero_of_not_sameFiber psi h0 h1 x s h, star_zero]

/-- Cast the integral Walsh sum to the complex character sum used by
`melTr_mul_star`. -/
lemma walsh_cast (x u : SS.BitString 6) :
    ((walsh x u : Int) : ℂ) =
      ∑ z : SS.BitString 6,
        ((Orbit21Coef.coef (num x) (num z) : Int) : ℂ) *
          ((chi z u : ℝ) : ℂ) := by
  unfold walsh
  push_cast
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [eps_cast]

/-- Swap a threefold finite sum from `z,s,t` to `s,t,z`. -/
lemma sum_comm3 {M : Type*} [AddCommMonoid M]
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → M) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  calc
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = ∑ b, ∑ c, ∑ a, f a b c :=
      Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

/-- **The corrected orbit-21 residual theorem.**

For arbitrary amplitudes supported anywhere inside the two full fibres, the
raw coefficient from `Orbit21Coef` annihilates the squared projector traces.
No KL equation, normalization, or unproved pointwise Pauli vanishing is used. -/
theorem residual_vanishes (psi : Fin 2 → SS.State 6 ℂ)
    (h0 : ∀ s, SS.weight Orbit21Cert.av s ≠ 0 → psi 0 s = 0)
    (h1 : ∀ s, SS.weight Orbit21Cert.av s ≠ 2 → psi 1 s = 0) :
    ∑ P : SS.PauliString 6,
      SixQubit.Orbit21Bridge.cf P * Complex.normSq (trProj psi P) = 0 := by
  have hC :
      (((∑ P : SS.PauliString 6,
          SixQubit.Orbit21Bridge.cf P * Complex.normSq (trProj psi P)) : ℝ) : ℂ) = 0 := by
    calc
      (((∑ P : SS.PauliString 6,
          SixQubit.Orbit21Bridge.cf P * Complex.normSq (trProj psi P)) : ℝ) : ℂ)
          = ∑ P : SS.PauliString 6,
              ((SixQubit.Orbit21Bridge.cf P : ℝ) : ℂ) *
                ((Complex.normSq (trProj psi P) : ℝ) : ℂ) := by push_cast; rfl
      _ = ∑ x : SS.BitString 6, ∑ z : SS.BitString 6,
              ((SixQubit.Orbit21Bridge.cf ⟨x, z⟩ : ℝ) : ℂ) *
                ((Complex.normSq (trProj psi ⟨x, z⟩) : ℝ) : ℂ) :=
            sum_pauli _
      _ = ∑ x : SS.BitString 6, ∑ z : SS.BitString 6,
              ((Orbit21Coef.coef (num x) (num z) : Int) : ℂ) *
                (∑ s : SS.BitString 6, ∑ t : SS.BitString 6,
                  ((chi z (SS.bxor s t) : ℝ) : ℂ) *
                    (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t)) := by
            refine Finset.sum_congr rfl (fun x _ =>
              Finset.sum_congr rfl (fun z _ => ?_))
            rw [normSq_trProj, normSq_cast, melTr_mul_star]
            rfl
      _ = ∑ x : SS.BitString 6, ∑ s : SS.BitString 6,
              ∑ t : SS.BitString 6, ∑ z : SS.BitString 6,
                (((Orbit21Coef.coef (num x) (num z) : Int) : ℂ) *
                    ((chi z (SS.bxor s t) : ℝ) : ℂ)) *
                  (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t) := by
            refine Finset.sum_congr rfl (fun x _ => ?_)
            simp_rw [Finset.mul_sum]
            rw [sum_comm3]
            refine Finset.sum_congr rfl (fun s _ =>
              Finset.sum_congr rfl (fun t _ =>
                Finset.sum_congr rfl (fun z _ => by ring)))
      _ = ∑ x : SS.BitString 6, ∑ s : SS.BitString 6,
              ∑ t : SS.BitString 6,
                ((walsh x (SS.bxor s t) : Int) : ℂ) *
                  (RR psi s (SS.bxor s x) * RR psi (SS.bxor t x) t) := by
            refine Finset.sum_congr rfl (fun x _ =>
              Finset.sum_congr rfl (fun s _ =>
                Finset.sum_congr rfl (fun t _ => ?_)))
            rw [walsh_cast, Finset.sum_mul]
      _ = 0 := by
            refine Finset.sum_eq_zero (fun x _ =>
              Finset.sum_eq_zero (fun s _ =>
                Finset.sum_eq_zero (fun t _ => ?_)))
            by_cases hs : sameFiber x s
            · by_cases ht : sameFiber x t
              · rw [walsh_zero_on_pairs x s t hs ht, Int.cast_zero, zero_mul]
              · rw [RR_reverse_zero_of_not_sameFiber psi h0 h1 x t ht,
                  mul_zero, mul_zero]
            · rw [RR_zero_of_not_sameFiber psi h0 h1 x s hs, zero_mul, mul_zero]
  exact_mod_cast hC

end SixQubit.Orbit21Residual
