import Orbit2.Encoder
import Orbit2.FiveQubitPhysical

namespace Orbit2.HilbertBridge
open scoped BigOperators
open Orbit2.TensorPauli

def bit : Bool → Fin 2 := fun b => if b then 1 else 0
def bitsEquiv (n : ℕ) : SS.BitString n ≃ (Fin n → Fin 2) where
  toFun x i := bit (x i)
  invFun s i := s i == 1
  left_inv x := by funext i; cases hx : x i <;> simp [bit, hx]
  right_inv s := by
    funext i
    change bit (s i == 1) = s i
    generalize s i = t
    fin_cases t <;> rfl

def labelSite (x z : Bool) : Fin 4 := if x then (if z then 2 else 1) else (if z then 3 else 0)
def label {n : ℕ} (p : SS.PauliString n) : Label n := fun i => labelSite (p.x i) (p.z i)

theorem label_injective {n : ℕ} : Function.Injective (@label n) := by
  intro p q h
  have hb : ∀ i, p.x i = q.x i ∧ p.z i = q.z i := by
    intro i
    have hi := congrFun h i
    cases hx : p.x i <;> cases hz : p.z i <;>
      cases hqx : q.x i <;> cases hqz : q.z i <;>
      simp_all [label, labelSite]
  cases p with
  | mk x z =>
    cases q with
    | mk x' z' =>
      have hx : x = x' := funext fun i => (hb i).1
      have hz : z = z' := funext fun i => (hb i).2
      simp_all
def flip {n : ℕ} (p : Label n) (s : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i => FiveQubit.flipSite (p i) (s i)

theorem flip_bits {n : ℕ} (p : SS.PauliString n) (x : SS.BitString n) :
    flip (label p) (bitsEquiv n x) = bitsEquiv n (SS.bxor x p.x) := by
  funext i
  cases hx : p.x i <;> cases hz : p.z i <;> cases ht : x i <;>
    simp [flip, label, labelSite, bitsEquiv, bit, FiveQubit.flipSite, SS.bxor, hx,hz,ht]

theorem local_phase_G : ∀ x z t : Bool,
    localG (labelSite x z) (bit t) (bit (xor t x)) =
      (⟨0,1⟩ : GaussianInt) ^ (if x && z then 1 else 0) *
        (if z && xor t x then -1 else 1) := by decide +kernel

theorem local_phase (x z t : Bool) :
    localC (labelSite x z) (bit t) (bit (xor t x)) =
      Complex.I ^ (if x && z then 1 else 0) * (if z && xor t x then -1 else 1) := by
  change (localG (labelSite x z) (bit t) (bit (xor t x)) : ℂ) = _
  rw [local_phase_G]
  cases x <;> cases z <;> cases t <;> norm_num [GaussianInt.toComplex_def]

theorem label_weight {n : ℕ} (p : SS.PauliString n) :
    (∑ i, if label p i = 0 then 0 else 1) = p.wt := by
  rw [SS.PauliString.wt, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : p.x i <;> cases hz : p.z i <;> simp [label, labelSite, hx,hz]

theorem operator_row {n : ℕ} (p : Label n) (s t : Fin n → Fin 2) :
    operator p s t = if t = flip p s then
      (∏ i, localC (p i) (s i) (flip p s i)) else 0 := by
  by_cases h : t = flip p s
  · simp [h, operator, tensor]
  · simp only [h, if_false]
    obtain ⟨i,hi⟩ : ∃ i, t i ≠ flip p s i := by
      by_contra hn; push_neg at hn; exact h (funext hn)
    unfold operator tensor
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [localC, Matrix.map_apply, FiveQubit.local_row_zero _ _ _ hi]

/-- The matrix and Hilbert-state definitions of a Pauli action coincide. -/
theorem pauli_action {n : ℕ} (p : SS.PauliString n) (φ : SS.State n ℂ) (x : SS.BitString n) :
    (∑ s, operator (label p) (bitsEquiv n x) s * φ ((bitsEquiv n).symm s)) =
      SS.pauliAct p φ x := by
  simp_rw [operator_row]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [flip_bits]
  simp only [Equiv.symm_apply_apply]
  have hprod : (∏ i, localC (label p i) (bitsEquiv n x i)
        (bitsEquiv n (SS.bxor x p.x) i)) =
      Complex.I ^ p.numY * (SS.MacWilliams.chi p.z (SS.bxor x p.x) : ℂ) := by
    change (∏ i, localC (labelSite (p.x i) (p.z i)) (bit (x i))
      (bit (xor (x i) (p.x i)))) = _
    simp_rw [local_phase, Finset.prod_mul_distrib]
    rw [Finset.prod_pow_eq_pow_sum]
    have hn : (∑ i, if p.x i && p.z i then 1 else 0) = p.numY := by
      simp only [SS.PauliString.numY, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hn]
    congr 1
    simp only [SS.MacWilliams.chi, SS.bxor, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> norm_num
  rw [hprod]
  simp only [SS.pauliAct, SS.MacWilliams.signC_bdot]
  ring

def words {n : ℕ} (Q : Matrix (Fin n → Fin 2) (Fin 2) ℂ) : Fin 2 → SS.State n ℂ :=
  fun j x => Q (bitsEquiv n x) j

theorem compression {n : ℕ} (Q : Matrix (Fin n → Fin 2) (Fin 2) ℂ)
    (p : SS.PauliString n) (j k : Fin 2) :
    SS.innerC (words Q j) (SS.pauliAct p (words Q k)) =
      (Q.conjTranspose * operator (label p) * Q) j k := by
  have haction : ∀ x, SS.pauliAct p (words Q k) x =
      (operator (label p) * Q) (bitsEquiv n x) k := by
    intro x
    simpa [words, Matrix.mul_apply] using (pauli_action p (words Q k) x).symm
  rw [Matrix.mul_assoc]
  simp only [SS.innerC, words, haction, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact (bitsEquiv n).sum_comp (fun s => star (Q s j) * ∑ t, operator (label p) s t * Q t k)

end Orbit2.HilbertBridge
