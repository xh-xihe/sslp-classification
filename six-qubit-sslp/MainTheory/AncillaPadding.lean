import MainTheory.TensorAppendZero
import MainTheory.CodeSpec
import SixQubit.Pin

/-!
# Padding an exact quantum code with a fixed zero ancilla

The state map is the literal computational-basis embedding `psi ↦ psi ⊗ |0⟩`.
The KL statement quantifies over every Pauli of the requested weight, including
errors acting on the new qubit. No hypothesis about a supplied padded code is used.
-/

namespace MainTheory.AncillaPadding

open scoped BigOperators
open MainTheory.TensorAppendZero MainTheory.CodeSpec

noncomputable section

variable {n K d : ℕ}

def snocPauli (P : SS.PauliString n) (x z : Bool) : SS.PauliString (n + 1) :=
  ⟨Fin.snoc P.x x, Fin.snoc P.z z⟩

def initPauli (P : SS.PauliString (n + 1)) : SS.PauliString n :=
  ⟨Fin.init P.x, Fin.init P.z⟩

@[simp] theorem snoc_initPauli (P : SS.PauliString (n + 1)) :
    snocPauli (initPauli P) (P.x (Fin.last n)) (P.z (Fin.last n)) = P := by
  cases P
  simp [snocPauli, initPauli]

theorem wt_snocPauli (P : SS.PauliString n) (x z : Bool) :
    (snocPauli P x z).wt = P.wt + if x || z then 1 else 0 := by
  simp only [SS.PauliString.wt, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [snocPauli]

theorem numY_snocPauli (P : SS.PauliString n) (x z : Bool) :
    (snocPauli P x z).numY = P.numY + if x && z then 1 else 0 := by
  simp only [SS.PauliString.numY, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [snocPauli]

theorem wt_initPauli_le (P : SS.PauliString (n + 1)) : (initPauli P).wt ≤ P.wt := by
  have h := wt_snocPauli (initPauli P) (P.x (Fin.last n)) (P.z (Fin.last n))
  rw [snoc_initPauli] at h
  omega

theorem bxor_snoc (s t : SS.BitString n) (a b : Bool) :
    SS.bxor (Fin.snoc s a) (Fin.snoc t b) = Fin.snoc (SS.bxor s t) (xor a b) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [SS.bxor]

theorem chi_snoc (s t : SS.BitString n) (a b : Bool) :
    SS.MacWilliams.chi (Fin.snoc s a) (Fin.snoc t b) =
      SS.MacWilliams.chi s t * if a && b then -1 else 1 := by
  simp only [SS.MacWilliams.chi]
  rw [Fin.prod_univ_castSucc]
  simp

theorem innerC_appendZero (f g : SS.State n ℂ) :
    SS.innerC (appendZero f) (appendZero g) = SS.innerC f g := by
  unfold SS.innerC
  rw [sum_snoc]
  simp [appendZero]

/-- Compression kills X/Y on the ancilla and leaves I/Z unchanged. -/
theorem compression_snocPauli (f g : SS.State n ℂ) (P : SS.PauliString n)
    (x z : Bool) :
    SS.innerC (appendZero f) (SS.pauliAct (snocPauli P x z) (appendZero g)) =
      if x then 0 else SS.innerC f (SS.pauliAct P g) := by
  unfold SS.innerC
  rw [sum_snoc]
  simp only [SS.pauliAct, snocPauli, bxor_snoc, SS.MacWilliams.signC_bdot,
    chi_snoc]
  have hY := numY_snocPauli P x z
  simp only [snocPauli] at hY
  rw [hY]
  cases x <;> cases z <;> simp [appendZero]

/-- Padding preserves every KL detection threshold, for an arbitrary frame. -/
theorem detects_appendZero (psi : Fin K → SS.State n ℂ) (w : ℕ)
    (h : SS.Detects psi w) : SS.Detects (fun k => appendZero (psi k)) w := by
  intro P hP
  obtain ⟨c, hc⟩ := h (initPauli P) ((wt_initPauli_le P).trans hP)
  refine ⟨if P.x (Fin.last n) then 0 else c, ?_⟩
  intro j k
  conv_lhs => rw [← snoc_initPauli P]
  rw [compression_snocPauli, hc]
  cases P.x (Fin.last n) <;> simp

theorem hasDistance_appendZero (psi : Fin K → SS.State n ℂ)
    (h : SS.HasDistance psi d) : SS.HasDistance (fun k => appendZero (psi k)) d :=
  detects_appendZero psi (d - 1) h

def appendFrame (F : OrthonormalFrame n K) : OrthonormalFrame (n + 1) K where
  vec k := appendZero (F.vec k)
  orthonormal j k := (innerC_appendZero _ _).trans (F.orthonormal j k)

def appendCode (C : ExactCode n K d) : ExactCode (n + 1) K d where
  positiveRank := C.positiveRank
  frame := appendFrame C.frame
  hasDistance := hasDistance_appendZero C.frame.vec C.hasDistance

def snocPauliEquiv : (Bool × Bool × SS.PauliString n) ≃ SS.PauliString (n + 1) where
  toFun p := snocPauli p.2.2 p.1 p.2.1
  invFun P := (P.x (Fin.last n), P.z (Fin.last n), initPauli P)
  left_inv p := by rcases p with ⟨x, z, P⟩; simp [snocPauli, initPauli]
  right_inv := snoc_initPauli

theorem trProj_appendZero (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n)
    (x z : Bool) :
    SS.MacWilliams.trProj (fun k => appendZero (psi k)) (snocPauli P x z) =
      if x then 0 else SS.MacWilliams.trProj psi P := by
  simp only [SS.MacWilliams.trProj, compression_snocPauli]
  cases x <;> simp

/-- The full unnormalised enumerator recurrence for one fixed zero ancilla. -/
theorem Aco_appendZero_succ (psi : Fin K → SS.State n ℂ) (w : ℕ) :
    SS.MacWilliams.Aco (fun k => appendZero (psi k)) (w + 1) =
      SS.MacWilliams.Aco psi (w + 1) + SS.MacWilliams.Aco psi w := by
  classical
  simp only [SS.MacWilliams.Aco, Finset.sum_filter]
  rw [← snocPauliEquiv.sum_comp]
  simp [Fintype.sum_prod_type, snocPauliEquiv, wt_snocPauli, trProj_appendZero]
  rw [add_comm]

theorem Aco_appendZero_zero (psi : Fin K → SS.State n ℂ) :
    SS.MacWilliams.Aco (fun k => appendZero (psi k)) 0 = SS.MacWilliams.Aco psi 0 := by
  classical
  simp only [SS.MacWilliams.Aco, Finset.sum_filter]
  rw [← snocPauliEquiv.sum_comp]
  simp [Fintype.sum_prod_type, snocPauliEquiv, wt_snocPauli, trProj_appendZero]

theorem Aco_frame_zero (F : OrthonormalFrame n K) :
    SS.MacWilliams.Aco F.vec 0 = (K : ℝ) ^ 2 := by
  classical
  have htr : SS.MacWilliams.trProj F.vec
      (⟨fun _ => false, fun _ => false⟩ : SS.PauliString n) = K := by
    have hid (k : Fin K) : SS.pauliAct
        (⟨fun _ => false, fun _ => false⟩ : SS.PauliString n) (F.vec k) = F.vec k := by
      ext t
      simp [SS.pauliAct, SS.PauliString.numY, SS.bdot, SS.signC]
    simp only [SS.MacWilliams.trProj, hid, F.orthonormal, if_true]
    simp
  simp only [SS.MacWilliams.Aco, SixQubit.Pin.wt_eq_zero_iff]
  simp only [Finset.filter_eq', Finset.mem_univ, if_true, Finset.sum_singleton, htr]
  simp [Complex.normSq_apply, pow_two]

/-- Each fixed pure ancilla contributes exactly one to the normalized A₁. -/
theorem AWeight_appendFrame_one (F : OrthonormalFrame n K) (hK : 0 < K) :
    AWeight (appendFrame F) 1 = AWeight F 1 + 1 := by
  have hk : (K : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hK)
  change SS.MacWilliams.Aco (fun k => appendZero (F.vec k)) (0 + 1) / _ = _
  rw [Aco_appendZero_succ, Aco_frame_zero, add_div, div_self hk]
  rfl

def padFrame (F : OrthonormalFrame n K) : (m : ℕ) → OrthonormalFrame (n + m) K
  | 0 => F
  | m + 1 => appendFrame (padFrame F m)

theorem hasDistance_padFrame (F : OrthonormalFrame n K) (h : SS.HasDistance F.vec d)
    (m : ℕ) : SS.HasDistance (padFrame F m).vec d := by
  induction m with
  | zero => exact h
  | succ m ih => exact hasDistance_appendZero (padFrame F m).vec ih

def padCode (C : ExactCode n K d) (m : ℕ) : ExactCode (n + m) K d where
  positiveRank := C.positiveRank
  frame := padFrame C.frame m
  hasDistance := hasDistance_padFrame C.frame C.hasDistance m

/-- The precise padding identity used by the manuscript's minimum-length proof. -/
theorem AWeight_padFrame_one (F : OrthonormalFrame n K) (hK : 0 < K) (m : ℕ) :
    AWeight (padFrame F m) 1 = AWeight F 1 + m := by
  induction m with
  | zero => simp [padFrame]
  | succ m ih =>
    change AWeight (appendFrame (padFrame F m)) 1 = _
    rw [AWeight_appendFrame_one _ hK, ih]
    push_cast
    ring

theorem AWeight_padFrame_one_pos (F : OrthonormalFrame n K) (hK : 0 < K)
    {m : ℕ} (hm : 0 < m) : 0 < AWeight (padFrame F m) 1 := by
  rw [AWeight_padFrame_one F hK]
  have hnonneg : 0 ≤ AWeight F 1 :=
    div_nonneg (SixQubit.Pin.Aco_nonneg F.vec 1) (sq_nonneg _)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  linarith

end

end MainTheory.AncillaPadding
