import SixQubit.Orbit8UniversalLadder

/-!
# Orbit 8 universal converse, V: the low-weight operator `Q`

The coordinate operator `Q = R R†` is expanded into one- and two-qubit
Paulis.  This makes equality of its two logical expectations a direct
consequence of genuine distance three.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators ComplexConjugate
open SixQubit

noncomputable section

def rl (i j : Fin 6) (f : SS.BitString 6 → ℂ) : SS.BitString 6 → ℂ :=
  fun x => if x i = true then
    if SS.bxor x (SS.stdBasis i) j = false then
      f (SS.bxor (SS.bxor x (SS.stdBasis i)) (SS.stdBasis j))
    else 0
  else 0

def projOne (i : Fin 6) (f : SS.BitString 6 → ℂ) : SS.BitString 6 → ℂ :=
  fun x => if x i = true then f x else 0

def hop (i j : Fin 6) (f : SS.BitString 6 → ℂ) : SS.BitString 6 → ℂ :=
  fun x => if x i = true ∧ x j = false then f (SS.bxor x (pairMask i j)) else 0

lemma Qact_expand (ud : Fin 6 → ℂ) (f : SS.BitString 6 → ℂ) :
    Qact ud f = fun x => ∑ i, ∑ j, ud i * star (ud j) * rl i j f x := by
  funext x
  classical
  unfold Qact raise lower rl
  refine Finset.sum_congr rfl (fun i hi => ?_)
  by_cases hxi : x i = true
  · rw [if_pos hxi, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    by_cases hxj : SS.bxor x (SS.stdBasis i) j = false
    · rw [if_pos hxj, if_pos hxi, if_pos hxj]
      ring
    · rw [if_neg hxj, if_pos hxi, if_neg hxj]
      ring
  · rw [if_neg hxi]
    simp [hxi]

lemma rl_self (i : Fin 6) (f : SS.BitString 6 → ℂ) : rl i i f = projOne i f := by
  funext x
  unfold rl projOne
  by_cases hxi : x i = true
  · rw [if_pos hxi, if_pos hxi]
    have htog : SS.bxor x (SS.stdBasis i) i = false := by
      simp [SS.bxor, SS.stdBasis, hxi]
    rw [if_pos htog, SS.bxor_bxor_cancel]
  · rw [if_neg hxi, if_neg hxi]

lemma rl_ne (i j : Fin 6) (hij : i ≠ j) (f : SS.BitString 6 → ℂ) :
    rl i j f = hop i j f := by
  funext x
  unfold rl hop pairMask
  by_cases hxi : x i = true
  · by_cases hxj : x j = false
    · have hboth : x i = true ∧ x j = false := ⟨hxi, hxj⟩
      rw [if_pos hxi, if_pos hboth]
      have htog : SS.bxor x (SS.stdBasis i) j = false := by
        simp [SS.bxor, SS.stdBasis, Ne.symm hij, hxj]
      rw [if_pos htog]
      rw [SS.bxor_assoc]
    · have hxjt : x j = true := Bool.eq_true_of_not_eq_false hxj
      have hnoth : ¬(x i = true ∧ x j = false) := by simp [hxjt]
      rw [if_pos hxi, if_neg hnoth]
      have htog : SS.bxor x (SS.stdBasis i) j ≠ false := by
        simp [SS.bxor, SS.stdBasis, Ne.symm hij, hxjt]
      rw [if_neg htog]
  · rw [if_neg hxi, if_neg (by simp [hxi])]

def Pz (i : Fin 6) : SS.PauliString 6 := ⟨zero6, SS.stdBasis i⟩
def Pxx (i j : Fin 6) : SS.PauliString 6 := ⟨pairMask i j, zero6⟩
def Pxy (i j : Fin 6) : SS.PauliString 6 := ⟨pairMask i j, SS.stdBasis j⟩
def Pyx (i j : Fin 6) : SS.PauliString 6 := ⟨pairMask i j, SS.stdBasis i⟩
def Pyy (i j : Fin 6) : SS.PauliString 6 := ⟨pairMask i j, pairMask i j⟩

theorem wt_Pz : ∀ i : Fin 6, (Pz i).wt ≤ 2 := by decide
theorem wt_Pxx : ∀ i j : Fin 6, (Pxx i j).wt ≤ 2 := by decide
theorem wt_Pxy : ∀ i j : Fin 6, (Pxy i j).wt ≤ 2 := by decide
theorem wt_Pyx : ∀ i j : Fin 6, (Pyx i j).wt ≤ 2 := by decide
theorem wt_Pyy : ∀ i j : Fin 6, (Pyy i j).wt ≤ 2 := by decide

theorem numY_Pz : ∀ i : Fin 6, (Pz i).numY = 0 := by decide
theorem numY_Pxx : ∀ i j : Fin 6, (Pxx i j).numY = 0 := by decide
theorem numY_Pxy : ∀ i j : Fin 6, i ≠ j → (Pxy i j).numY = 1 := by decide
theorem numY_Pyx : ∀ i j : Fin 6, i ≠ j → (Pyx i j).numY = 1 := by decide
theorem numY_Pyy : ∀ i j : Fin 6, i ≠ j → (Pyy i j).numY = 2 := by decide

lemma act_Pz (i : Fin 6) (f : SS.BitString 6 → ℂ) (x : SS.BitString 6) :
    SS.pauliAct (Pz i) f x = if x i = true then -f x else f x := by
  unfold SS.pauliAct Pz
  rw [show (⟨zero6, SS.stdBasis i⟩ : SS.PauliString 6).numY = 0 from numY_Pz i]
  simp only [pow_zero, one_mul]
  rw [show zero6 = (fun _ => false) from rfl, SS.bxor_zero]
  rw [bdot_stdBasis]
  cases hxi : x i <;> simp [SS.signC]

lemma projOne_pauli (i : Fin 6) (f : SS.BitString 6 → ℂ) :
    projOne i f = fun x => (f x - SS.pauliAct (Pz i) f x) / 2 := by
  funext x
  rw [act_Pz]
  unfold projOne
  by_cases hxi : x i = true <;> simp [hxi]

lemma act_Pxx (i j : Fin 6) (f : SS.BitString 6 → ℂ) (x : SS.BitString 6) :
    SS.pauliAct (Pxx i j) f x = f (SS.bxor x (pairMask i j)) := by
  unfold SS.pauliAct Pxx
  rw [show (⟨pairMask i j, zero6⟩ : SS.PauliString 6).numY = 0 from numY_Pxx i j]
  simp [zero6, SS.bdot]

lemma act_Pxy (i j : Fin 6) (hij : i ≠ j)
    (f : SS.BitString 6 → ℂ) (x : SS.BitString 6) :
    SS.pauliAct (Pxy i j) f x =
      if x j = true then Complex.I * f (SS.bxor x (pairMask i j))
      else -Complex.I * f (SS.bxor x (pairMask i j)) := by
  unfold SS.pauliAct Pxy
  rw [show (⟨pairMask i j, SS.stdBasis j⟩ : SS.PauliString 6).numY = 1 from
    numY_Pxy i j hij, pow_one, bdot_stdBasis]
  have hbit : SS.bxor (SS.bxor x (SS.stdBasis i)) (SS.stdBasis j) j = !x j := by
    rw [SS.bxor_apply, SS.bxor_apply, SS.stdBasis_apply_self,
      SS.stdBasis_apply_ne (Ne.symm hij)]
    simp
  rw [show SS.bxor x (pairMask i j) =
      SS.bxor (SS.bxor x (SS.stdBasis i)) (SS.stdBasis j) by
    rw [pairMask, SS.bxor_assoc]]
  rw [hbit]
  cases hxj : x j <;> simp [SS.signC]

lemma act_Pyx (i j : Fin 6) (hij : i ≠ j)
    (f : SS.BitString 6 → ℂ) (x : SS.BitString 6) :
    SS.pauliAct (Pyx i j) f x =
      if x i = true then Complex.I * f (SS.bxor x (pairMask i j))
      else -Complex.I * f (SS.bxor x (pairMask i j)) := by
  unfold SS.pauliAct Pyx
  rw [show (⟨pairMask i j, SS.stdBasis i⟩ : SS.PauliString 6).numY = 1 from
    numY_Pyx i j hij, pow_one, bdot_stdBasis]
  have hbit : SS.bxor (SS.bxor x (SS.stdBasis i)) (SS.stdBasis j) i = !x i := by
    rw [SS.bxor_apply, SS.bxor_apply, SS.stdBasis_apply_ne hij,
      SS.stdBasis_apply_self]
    simp
  rw [show SS.bxor x (pairMask i j) =
      SS.bxor (SS.bxor x (SS.stdBasis i)) (SS.stdBasis j) by
    rw [pairMask, SS.bxor_assoc]]
  rw [hbit]
  cases hxi : x i <;> simp [SS.signC]

lemma act_Pyy (i j : Fin 6) (hij : i ≠ j)
    (f : SS.BitString 6 → ℂ) (x : SS.BitString 6) :
    SS.pauliAct (Pyy i j) f x =
      if xor (x i) (x j) = true then f (SS.bxor x (pairMask i j))
      else -f (SS.bxor x (pairMask i j)) := by
  unfold SS.pauliAct Pyy
  rw [show (⟨pairMask i j, pairMask i j⟩ : SS.PauliString 6).numY = 2 from
    numY_Pyy i j hij]
  norm_num [Complex.I_mul_I]
  rw [show pairMask i j = SS.bxor (SS.stdBasis i) (SS.stdBasis j) from rfl]
  rw [bdot_stdBasis_pair]
  cases hxi : x i <;> cases hxj : x j <;>
    simp [SS.bxor, SS.stdBasis, hij, Ne.symm hij, hxi, hxj, SS.signC]

lemma hop_pauli (i j : Fin 6) (hij : i ≠ j) (f : SS.BitString 6 → ℂ) :
    hop i j f = fun x =>
      (SS.pauliAct (Pxx i j) f x + Complex.I * SS.pauliAct (Pxy i j) f x
        - Complex.I * SS.pauliAct (Pyx i j) f x + SS.pauliAct (Pyy i j) f x) / 4 := by
  funext x
  rw [act_Pxx, act_Pxy i j hij, act_Pyx i j hij, act_Pyy i j hij]
  unfold hop
  cases hxi : x i <;> cases hxj : x j <;>
    simp [← mul_assoc, Complex.I_mul_I]
  all_goals ring

/-- The two diagonal expectations supplied by a genuine distance-three code
are equal for every Pauli of weight at most two. -/
lemma expect_eq_of_hasDistance (c d : SS.BitString 6 → ℂ)
    (hcode : SS.HasDistance ![c,d] 3) (P : SS.PauliString 6) (hw : P.wt ≤ 2) :
    SS.innerC c (SS.pauliAct P c) = SS.innerC d (SS.pauliAct P d) := by
  have hdet : SS.Detects (![c,d] : Fin 2 → SS.State 6 ℂ) 2 := hcode
  obtain ⟨z, hz⟩ := hdet P hw
  have h0 := hz 0 0
  have h1 := hz 1 1
  simp only [pair_zero, pair_one] at h0 h1
  exact h0.trans h1.symm

lemma inner_projOne (f : SS.BitString 6 → ℂ) (i : Fin 6) :
    SS.innerC f (projOne i f) =
      (SS.innerC f f - SS.innerC f (SS.pauliAct (Pz i) f)) / 2 := by
  rw [projOne_pauli]
  unfold SS.innerC
  change (∑ x, star (f x) * ((f x - SS.pauliAct (Pz i) f x) / 2)) = _
  calc
    (∑ x, star (f x) * ((f x - SS.pauliAct (Pz i) f x) / 2)) =
        ∑ x, (star (f x) * f x - star (f x) * SS.pauliAct (Pz i) f x) / 2 := by
      refine Finset.sum_congr rfl (fun x hx => by ring)
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_sub_distrib]

lemma inner_hop (f : SS.BitString 6 → ℂ) (i j : Fin 6) (hij : i ≠ j) :
    SS.innerC f (hop i j f) =
      (SS.innerC f (SS.pauliAct (Pxx i j) f)
        + Complex.I * SS.innerC f (SS.pauliAct (Pxy i j) f)
        - Complex.I * SS.innerC f (SS.pauliAct (Pyx i j) f)
        + SS.innerC f (SS.pauliAct (Pyy i j) f)) / 4 := by
  rw [hop_pauli i j hij]
  unfold SS.innerC
  change (∑ x, star (f x) *
    ((SS.pauliAct (Pxx i j) f x + Complex.I * SS.pauliAct (Pxy i j) f x
      - Complex.I * SS.pauliAct (Pyx i j) f x + SS.pauliAct (Pyy i j) f x) / 4)) = _
  calc
    _ = ∑ x, (star (f x) * SS.pauliAct (Pxx i j) f x
        + Complex.I * (star (f x) * SS.pauliAct (Pxy i j) f x)
        - Complex.I * (star (f x) * SS.pauliAct (Pyx i j) f x)
        + star (f x) * SS.pauliAct (Pyy i j) f x) / 4 := by
      refine Finset.sum_congr rfl (fun x hx => by ring)
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

lemma inner_rl_eq (c d : SS.BitString 6 → ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (i j : Fin 6) :
    SS.innerC c (rl i j c) = SS.innerC d (rl i j d) := by
  by_cases hij : i = j
  · subst j
    rw [rl_self, rl_self, inner_projOne, inner_projOne]
    rw [hnc, hnd, expect_eq_of_hasDistance c d hcode (Pz i) (wt_Pz i)]
  · rw [rl_ne i j hij, rl_ne i j hij, inner_hop c i j hij, inner_hop d i j hij]
    rw [expect_eq_of_hasDistance c d hcode (Pxx i j) (wt_Pxx i j)]
    rw [expect_eq_of_hasDistance c d hcode (Pxy i j) (wt_Pxy i j)]
    rw [expect_eq_of_hasDistance c d hcode (Pyx i j) (wt_Pyx i j)]
    rw [expect_eq_of_hasDistance c d hcode (Pyy i j) (wt_Pyy i j)]

lemma inner_Q_expand (f : SS.BitString 6 → ℂ) (ud : Fin 6 → ℂ) :
    SS.innerC f (Qact ud f) =
      ∑ i, ∑ j, ud i * star (ud j) * SS.innerC f (rl i j f) := by
  rw [Qact_expand]
  unfold SS.innerC
  change (∑ x, star (f x) *
    (∑ i, ∑ j, ud i * star (ud j) * rl i j f x)) = _
  calc
    _ = ∑ x, ∑ i, ∑ j,
        ud i * star (ud j) * (star (f x) * rl i j f x) := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => by ring)
    _ = ∑ i, ∑ j, ∑ x,
        ud i * star (ud j) * (star (f x) * rl i j f x) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i hi => by rw [Finset.sum_comm])
    _ = _ := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mul_sum]

/-- `Q` has equal expectation on the two logical states, because all its
Pauli components have weight at most two. -/
theorem Q_expect_eq (c d : SS.BitString 6 → ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) (ud : Fin 6 → ℂ) :
    SS.innerC c (Qact ud c) = SS.innerC d (Qact ud d) := by
  rw [inner_Q_expand, inner_Q_expand]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [inner_rl_eq c d hnc hnd hcode i j]

end

end SixQubit.Orbit8Universal
