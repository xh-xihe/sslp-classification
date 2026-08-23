import SixQubit.BEnumerator

/-!
# Equivalence as an honest relation and enumerator transport

`SixQubit.CodeEquiv` defines the concrete change of gauge used by the orbit
classification.  This file supplies the group-law lemmas and the weight-
enumerator invariance facts.  It deliberately remains over the ordinary Lean
kernel: no native decision procedure and no additional axioms are used.
-/

namespace SixQubit.CodeEquiv

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## 1. Composition and inversion of local monomial actions -/

lemma permStr_trans (σ τ : Equiv.Perm (Fin n)) (s : SS.BitString n) :
    permStr σ (permStr τ s) = permStr (σ.trans τ) s := by
  rfl

lemma LocalMonomial.act_scal (U : LocalMonomial n) (l : ℂ) (psi : SS.State n ℂ) :
    U.act (scal l psi) = scal l (U.act psi) := by
  funext s
  simp only [LocalMonomial.act_apply, scal]
  ring

/-- Composition in action order: `(V.comp U).act = V.act ∘ U.act`. -/
def LocalMonomial.comp (V U : LocalMonomial n) : LocalMonomial n where
  perm := U.perm.trans V.perm
  flip := SS.bxor V.flip (permStr V.perm.symm U.flip)
  al := fun i => V.al i *
    (if V.flip i then U.be (V.perm.symm i) else U.al (V.perm.symm i))
  be := fun i => V.be i *
    (if V.flip i then U.al (V.perm.symm i) else U.be (V.perm.symm i))
  al_unit := by
    intro i
    rw [map_mul, V.al_unit]
    split
    · rw [U.be_unit]; norm_num
    · rw [U.al_unit]; norm_num
  be_unit := by
    intro i
    rw [map_mul, V.be_unit]
    split
    · rw [U.al_unit]; norm_num
    · rw [U.be_unit]; norm_num

private lemma LocalMonomial.comp_arg (V U : LocalMonomial n) (s : SS.BitString n) :
    permStr (V.comp U).perm (SS.bxor s (V.comp U).flip) =
      permStr U.perm
        (SS.bxor (permStr V.perm (SS.bxor s V.flip)) U.flip) := by
  funext i
  simp only [LocalMonomial.comp, permStr, SS.bxor, Equiv.trans_apply]
  rw [V.perm.symm_apply_apply]
  exact (Bool.xor_assoc _ _ _).symm

private lemma LocalMonomial.comp_phase (V U : LocalMonomial n) (s : SS.BitString n) :
    (∏ i, if s i then (V.comp U).be i else (V.comp U).al i) =
      (∏ i, if s i then V.be i else V.al i) *
        (∏ i, if (permStr V.perm (SS.bxor s V.flip)) i then U.be i else U.al i) := by
  let g : Fin n → ℂ := fun i =>
    if (permStr V.perm (SS.bxor s V.flip)) i then U.be i else U.al i
  have hreindex :
      (∏ i, if (permStr V.perm (SS.bxor s V.flip)) i then U.be i else U.al i) =
        ∏ i, if SS.bxor s V.flip i then U.be (V.perm.symm i)
          else U.al (V.perm.symm i) := by
    have h := Equiv.prod_comp V.perm.symm g
    rw [show (∏ i, if (permStr V.perm (SS.bxor s V.flip)) i then U.be i
        else U.al i) = ∏ i, g i by rfl]
    rw [← h]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp only [g, permStr, Equiv.apply_symm_apply]
  rw [hreindex, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [LocalMonomial.comp]
  cases hs : s i <;> cases hf : V.flip i <;> simp [hs, hf, SS.bxor]

theorem LocalMonomial.comp_act (V U : LocalMonomial n) (psi : SS.State n ℂ) :
    (V.comp U).act psi = V.act (U.act psi) := by
  funext s
  simp only [LocalMonomial.act_apply]
  rw [LocalMonomial.comp_phase]
  rw [LocalMonomial.comp_arg]
  ring

/-- The inverse local monomial transformation. -/
def LocalMonomial.inv (U : LocalMonomial n) : LocalMonomial n where
  perm := U.perm.symm
  flip := permStr U.perm U.flip
  al := fun i =>
    if U.flip (U.perm i) then star (U.be (U.perm i)) else star (U.al (U.perm i))
  be := fun i =>
    if U.flip (U.perm i) then star (U.al (U.perm i)) else star (U.be (U.perm i))
  al_unit := by
    intro i
    split
    · change Complex.normSq ((starRingEnd ℂ) (U.be (U.perm i))) = 1
      rw [Complex.normSq_conj, U.be_unit]
    · change Complex.normSq ((starRingEnd ℂ) (U.al (U.perm i))) = 1
      rw [Complex.normSq_conj, U.al_unit]
  be_unit := by
    intro i
    split
    · change Complex.normSq ((starRingEnd ℂ) (U.al (U.perm i))) = 1
      rw [Complex.normSq_conj, U.al_unit]
    · change Complex.normSq ((starRingEnd ℂ) (U.be (U.perm i))) = 1
      rw [Complex.normSq_conj, U.be_unit]

private lemma LocalMonomial.inv_arg (U : LocalMonomial n) (s : SS.BitString n) :
    permStr U.perm
        (SS.bxor (permStr U.inv.perm (SS.bxor s U.inv.flip)) U.flip) = s := by
  funext i
  simp only [LocalMonomial.inv, permStr, SS.bxor, Equiv.symm_apply_apply]
  cases s i <;> cases U.flip (U.perm i) <;> rfl

private lemma LocalMonomial.inv_phase (U : LocalMonomial n) (s : SS.BitString n) :
    (∏ i, if s i then U.inv.be i else U.inv.al i) *
        (∏ i, if (permStr U.inv.perm (SS.bxor s U.inv.flip)) i
          then U.be i else U.al i) = 1 := by
  let y : SS.BitString n := permStr U.inv.perm (SS.bxor s U.inv.flip)
  let g : Fin n → ℂ := fun i => if y i then U.be i else U.al i
  have hreindex : (∏ i, if y i then U.be i else U.al i) = ∏ i, g (U.perm i) := by
    exact (Equiv.prod_comp U.perm g).symm
  change (∏ i, if s i then U.inv.be i else U.inv.al i) *
      (∏ i, if y i then U.be i else U.al i) = 1
  rw [hreindex, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i hi
  simp only [LocalMonomial.inv, g, y, permStr, SS.bxor, Equiv.symm_apply_apply]
  cases s i <;> cases U.flip (U.perm i) <;> simp only [
    Bool.false_eq_true, if_false, if_true, Bool.false_xor,
    Bool.true_xor, Bool.not_false, Bool.not_true]
  · exact unit_of_normSq (U.al_unit _)
  · exact unit_of_normSq (U.be_unit _)
  · exact unit_of_normSq (U.be_unit _)
  · exact unit_of_normSq (U.al_unit _)

theorem LocalMonomial.inv_act (U : LocalMonomial n) (psi : SS.State n ℂ) :
    U.inv.act (U.act psi) = psi := by
  funext s
  simp only [LocalMonomial.act_apply]
  rw [← mul_assoc, LocalMonomial.inv_phase, LocalMonomial.inv_arg, one_mul]

/-! ## 2. `Equivalent` is an equivalence relation -/

lemma swapIdx_xor (a b : Bool) (k : Fin 2) :
    swapIdx a (swapIdx b k) = swapIdx (xor a b) k := by
  cases a <;> cases b <;> fin_cases k <;> rfl

theorem Equivalent.symm {p q : Fin 2 → SS.State n ℂ} (h : Equivalent p q) :
    Equivalent q p := by
  obtain ⟨U, lam, sw, hlam, hq⟩ := h
  refine ⟨U.inv, fun k => star (lam (swapIdx sw k)), sw, ?_, ?_⟩
  · intro k
    change Complex.normSq ((starRingEnd ℂ) (lam (swapIdx sw k))) = 1
    rw [Complex.normSq_conj, hlam]
  · intro k
    rw [hq (swapIdx sw k), swapIdx_involutive]
    rw [U.inv.act_scal, U.inv_act]
    funext s
    simp only [scal]
    rw [← mul_assoc, star_mul_self, hlam]
    norm_num

theorem Equivalent.trans {p q r : Fin 2 → SS.State n ℂ}
    (hpq : Equivalent p q) (hqr : Equivalent q r) : Equivalent p r := by
  obtain ⟨U, lam, sw, hlam, hq⟩ := hpq
  obtain ⟨V, mu, tw, hmu, hr⟩ := hqr
  refine ⟨V.comp U, fun k => mu k * lam (swapIdx tw k), xor sw tw, ?_, ?_⟩
  · intro k
    rw [map_mul, hmu, hlam]
    norm_num
  · intro k
    rw [hr k, hq (swapIdx tw k)]
    rw [V.act_scal, ← V.comp_act]
    rw [swapIdx_xor]
    funext s
    simp only [scal]
    ring

/-! ## 3. Elementary matrix-element transport -/

open SS.MacWilliams

lemma mel_eq_corr (u v : SS.State n ℂ) (P : SS.PauliString n) :
    mel u v P = corr u v P.x P.z := by
  rw [mel, corr]
  exact Finset.sum_congr rfl (fun s _ => (signC_bdot P.z s _).symm)

lemma mel_scal (l m : ℂ) (u v : SS.State n ℂ) (P : SS.PauliString n) :
    mel (scal l u) (scal m v) P = star l * m * mel u v P := by
  rw [mel_eq_corr, corr_scal, mel_eq_corr]

lemma mel_permAct (σ : Equiv.Perm (Fin n)) (u v : SS.State n ℂ)
    (P : SS.PauliString n) :
    mel (permAct σ u) (permAct σ v) P =
      mel u v ⟨permStr σ P.x, permStr σ P.z⟩ := by
  rw [mel_eq_corr, corr_permAct, mel_eq_corr]

lemma mel_flipAct (f : SS.BitString n) (u v : SS.State n ℂ)
    (P : SS.PauliString n) :
    mel (flipAct f u) (flipAct f v) P = SS.signC (SS.bdot P.z f) (mel u v P) := by
  rw [mel_eq_corr, corr_flipAct, mel_eq_corr]

lemma normSq_mel_scal {l m : ℂ} (hl : Complex.normSq l = 1)
    (hm : Complex.normSq m = 1) (u v : SS.State n ℂ) (P : SS.PauliString n) :
    Complex.normSq (mel (scal l u) (scal m v) P) = Complex.normSq (mel u v P) := by
  rw [mel_scal, map_mul, map_mul]
  change Complex.normSq ((starRingEnd ℂ) l) * Complex.normSq m *
      Complex.normSq (mel u v P) = Complex.normSq (mel u v P)
  rw [Complex.normSq_conj, hl, hm]
  norm_num

lemma normSq_mel_flipAct (f : SS.BitString n) (u v : SS.State n ℂ)
    (P : SS.PauliString n) :
    Complex.normSq (mel (flipAct f u) (flipAct f v) P) =
      Complex.normSq (mel u v P) := by
  rw [mel_flipAct]
  cases SS.bdot P.z f <;> simp [SS.signC]

def swapEquiv (b : Bool) : Fin 2 ≃ Fin 2 where
  toFun := swapIdx b
  invFun := swapIdx b
  left_inv := swapIdx_involutive b
  right_inv := swapIdx_involutive b

/-! ## 4. Logical phases and swaps -/

lemma trProj_phase {K : ℕ} (psi : Fin K → SS.State n ℂ) (lam : Fin K → ℂ)
    (hlam : ∀ k, Complex.normSq (lam k) = 1) (P : SS.PauliString n) :
    trProj (fun k => scal (lam k) (psi k)) P = trProj psi P := by
  rw [trProj_eq, trProj_eq]
  congr 1
  rw [melTr, melTr]
  exact Finset.sum_congr rfl (fun k _ => by
    rw [mel_scal, unit_of_normSq (hlam k), one_mul])

lemma frob_phase {K : ℕ} (psi : Fin K → SS.State n ℂ) (lam : Fin K → ℂ)
    (hlam : ∀ k, Complex.normSq (lam k) = 1) (P : SS.PauliString n) :
    frob (fun k => scal (lam k) (psi k)) P = frob psi P := by
  rw [frob, frob]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
    rw [normSq_innerC, normSq_innerC, normSq_mel_scal (hlam a) (hlam b)]))

lemma trProj_swap (psi : Fin 2 → SS.State n ℂ) (b : Bool) (P : SS.PauliString n) :
    trProj (fun k => psi (swapIdx b k)) P = trProj psi P := by
  rw [trProj, trProj]
  exact Equiv.sum_comp (swapEquiv b)
    (fun k => SS.innerC (psi k) (SS.pauliAct P (psi k)))

lemma frob_swap (psi : Fin 2 → SS.State n ℂ) (c : Bool) (P : SS.PauliString n) :
    frob (fun k => psi (swapIdx c k)) P = frob psi P := by
  rw [frob, frob]
  let e := swapEquiv c
  calc
    (∑ a, ∑ b, Complex.normSq
        (SS.innerC (psi (e a)) (SS.pauliAct P (psi (e b)))))
        = ∑ a, ∑ b, Complex.normSq
            (SS.innerC (psi (e a)) (SS.pauliAct P (psi b))) := by
              refine Finset.sum_congr rfl (fun a _ => ?_)
              let g : Fin 2 → ℝ := fun b => Complex.normSq
                (SS.innerC (psi (e a)) (SS.pauliAct P (psi b)))
              change (∑ b, g (e b)) = ∑ b, g b
              exact Equiv.sum_comp e g
    _ = ∑ a, ∑ b, Complex.normSq
          (SS.innerC (psi a) (SS.pauliAct P (psi b))) := by
            let g : Fin 2 → ℝ := fun a => ∑ b, Complex.normSq
              (SS.innerC (psi a) (SS.pauliAct P (psi b)))
            change (∑ a, g (e a)) = ∑ a, g a
            exact Equiv.sum_comp e g

theorem Aco_phase {K : ℕ} (psi : Fin K → SS.State n ℂ) (lam : Fin K → ℂ)
    (hlam : ∀ k, Complex.normSq (lam k) = 1) (j : ℕ) :
    Aco (fun k => scal (lam k) (psi k)) j = Aco psi j := by
  rw [Aco, Aco]
  exact Finset.sum_congr rfl (fun P _ => by rw [trProj_phase psi lam hlam])

theorem Bco_phase {K : ℕ} (psi : Fin K → SS.State n ℂ) (lam : Fin K → ℂ)
    (hlam : ∀ k, Complex.normSq (lam k) = 1) (j : ℕ) :
    Bco (fun k => scal (lam k) (psi k)) j = Bco psi j := by
  rw [Bco, Bco]
  congr 1
  exact Finset.sum_congr rfl (fun P _ => frob_phase psi lam hlam P)

theorem Aco_swap (psi : Fin 2 → SS.State n ℂ) (b : Bool) (j : ℕ) :
    Aco (fun k => psi (swapIdx b k)) j = Aco psi j := by
  rw [Aco, Aco]
  exact Finset.sum_congr rfl (fun P _ => by rw [trProj_swap])

theorem Bco_swap (psi : Fin 2 → SS.State n ℂ) (b : Bool) (j : ℕ) :
    Bco (fun k => psi (swapIdx b k)) j = Bco psi j := by
  rw [Bco, Bco]
  congr 1
  exact Finset.sum_congr rfl (fun P _ => frob_swap psi b P)

/-! ## 5. Physical permutations and Pauli flips -/

def permPauliEquiv (σ : Equiv.Perm (Fin n)) :
    SS.PauliString n ≃ SS.PauliString n where
  toFun P := ⟨permStr σ P.x, permStr σ P.z⟩
  invFun P := ⟨permStr σ.symm P.x, permStr σ.symm P.z⟩
  left_inv := by
    rintro ⟨x, z⟩
    change (⟨permStr σ.symm (permStr σ x), permStr σ.symm (permStr σ z)⟩ :
      SS.PauliString n) = ⟨x, z⟩
    rw [SS.PauliString.mk.injEq]
    constructor <;> funext i <;> simp [permStr]
  right_inv := by
    rintro ⟨x, z⟩
    change (⟨permStr σ (permStr σ.symm x), permStr σ (permStr σ.symm z)⟩ :
      SS.PauliString n) = ⟨x, z⟩
    rw [SS.PauliString.mk.injEq]
    constructor <;> funext i <;> simp [permStr]

lemma permPauliEquiv_wt (σ : Equiv.Perm (Fin n)) (P : SS.PauliString n) :
    (permPauliEquiv σ P).wt = P.wt := by
  exact wt_permStr σ P.x P.z

lemma normSq_trProj_permAct {K : ℕ} (σ : Equiv.Perm (Fin n))
    (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    Complex.normSq (trProj (fun k => permAct σ (psi k)) P) =
      Complex.normSq (trProj psi (permPauliEquiv σ P)) := by
  rw [normSq_trProj, normSq_trProj]
  congr 1
  rw [melTr, melTr]
  exact Finset.sum_congr rfl (fun k _ => mel_permAct σ _ _ P)

lemma frob_permAct {K : ℕ} (σ : Equiv.Perm (Fin n))
    (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    frob (fun k => permAct σ (psi k)) P = frob psi (permPauliEquiv σ P) := by
  rw [frob, frob]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
    rw [normSq_innerC, normSq_innerC]
    congr 1
    exact mel_permAct σ _ _ P))

lemma normSq_trProj_flipAct {K : ℕ} (f : SS.BitString n)
    (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    Complex.normSq (trProj (fun k => flipAct f (psi k)) P) =
      Complex.normSq (trProj psi P) := by
  rw [normSq_trProj, normSq_trProj]
  rw [melTr, melTr]
  have hsum :
      (∑ k, mel (flipAct f (psi k)) (flipAct f (psi k)) P) =
        SS.signC (SS.bdot P.z f) (∑ k, mel (psi k) (psi k) P) := by
    cases hb : SS.bdot P.z f
    · simp only [mel_flipAct, hb, SS.signC_false]
    · simp only [mel_flipAct, hb, SS.signC_true, Finset.sum_neg_distrib]
  rw [hsum]
  cases SS.bdot P.z f <;> simp [SS.signC]

lemma frob_flipAct {K : ℕ} (f : SS.BitString n)
    (psi : Fin K → SS.State n ℂ) (P : SS.PauliString n) :
    frob (fun k => flipAct f (psi k)) P = frob psi P := by
  rw [frob, frob]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by
    rw [normSq_innerC, normSq_innerC, normSq_mel_flipAct]))

theorem Aco_permAct {K : ℕ} (σ : Equiv.Perm (Fin n))
    (psi : Fin K → SS.State n ℂ) (j : ℕ) :
    Aco (fun k => permAct σ (psi k)) j = Aco psi j := by
  rw [Aco, Aco, Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ P, if P.wt = j then
        Complex.normSq (trProj (fun k => permAct σ (psi k)) P) else 0)
      = ∑ P, if (permPauliEquiv σ P).wt = j then
          Complex.normSq (trProj psi (permPauliEquiv σ P)) else 0 := by
            exact Finset.sum_congr rfl (fun P _ => by
              rw [permPauliEquiv_wt, normSq_trProj_permAct])
    _ = ∑ P, if P.wt = j then Complex.normSq (trProj psi P) else 0 :=
      by
        let g : SS.PauliString n → ℝ := fun P =>
          if P.wt = j then Complex.normSq (trProj psi P) else 0
        change (∑ P, g (permPauliEquiv σ P)) = ∑ P, g P
        exact Equiv.sum_comp (permPauliEquiv σ) g

theorem Bco_permAct {K : ℕ} (σ : Equiv.Perm (Fin n))
    (psi : Fin K → SS.State n ℂ) (j : ℕ) :
    Bco (fun k => permAct σ (psi k)) j = Bco psi j := by
  rw [Bco, Bco]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ P, if P.wt = j then frob (fun k => permAct σ (psi k)) P else 0)
      = ∑ P, if (permPauliEquiv σ P).wt = j then
          frob psi (permPauliEquiv σ P) else 0 := by
            exact Finset.sum_congr rfl (fun P _ => by
              rw [permPauliEquiv_wt, frob_permAct])
    _ = ∑ P, if P.wt = j then frob psi P else 0 :=
      by
        let g : SS.PauliString n → ℝ := fun P =>
          if P.wt = j then frob psi P else 0
        change (∑ P, g (permPauliEquiv σ P)) = ∑ P, g P
        exact Equiv.sum_comp (permPauliEquiv σ) g

theorem Aco_flipAct {K : ℕ} (f : SS.BitString n)
    (psi : Fin K → SS.State n ℂ) (j : ℕ) :
    Aco (fun k => flipAct f (psi k)) j = Aco psi j := by
  rw [Aco, Aco]
  exact Finset.sum_congr rfl (fun P _ => normSq_trProj_flipAct f psi P)

theorem Bco_flipAct {K : ℕ} (f : SS.BitString n)
    (psi : Fin K → SS.State n ℂ) (j : ℕ) :
    Bco (fun k => flipAct f (psi k)) j = Bco psi j := by
  rw [Bco, Bco]
  congr 1
  exact Finset.sum_congr rfl (fun P _ => frob_flipAct f psi P)

theorem Aco_flip_permAct {K : ℕ} (σ : Equiv.Perm (Fin n)) (f : SS.BitString n)
    (psi : Fin K → SS.State n ℂ) (j : ℕ) :
    Aco (fun k => flipAct f (permAct σ (psi k))) j = Aco psi j := by
  rw [Aco_flipAct, Aco_permAct]

theorem Bco_flip_permAct {K : ℕ} (σ : Equiv.Perm (Fin n)) (f : SS.BitString n)
    (psi : Fin K → SS.State n ℂ) (j : ℕ) :
    Bco (fun k => flipAct f (permAct σ (psi k))) j = Bco psi j := by
  rw [Bco_flipAct, Bco_permAct]

/-- `Aco` is invariant under the exact fixed gauge layer used for orbit 36:
a logical swap, a qubit permutation and a cube translation. -/
theorem Aco_fixed_perm_flip_swap (σ : Equiv.Perm (Fin n)) (f : SS.BitString n)
    (psi : Fin 2 → SS.State n ℂ) (sw : Bool) (j : ℕ) :
    Aco (fun k => flipAct f (permAct σ (psi (swapIdx sw k)))) j = Aco psi j := by
  rw [Aco_flip_permAct, Aco_swap]

/-- `Bco` version of `Aco_fixed_perm_flip_swap`. -/
theorem Bco_fixed_perm_flip_swap (σ : Equiv.Perm (Fin n)) (f : SS.BitString n)
    (psi : Fin 2 → SS.State n ℂ) (sw : Bool) (j : ℕ) :
    Bco (fun k => flipAct f (permAct σ (psi (swapIdx sw k)))) j = Bco psi j := by
  rw [Bco_flip_permAct, Bco_swap]

/-! ## 6. The normalized two-word `AEnum` wrappers -/

private lemma AEnum_eq_of_Aco_eq {c d e f : SS.State 6 ℂ} {j : ℕ}
    (h : Aco ![c, d] j = Aco ![e, f] j) :
    SixQubit.Orbit36Phase.AEnum c d j = SixQubit.Orbit36Phase.AEnum e f j := by
  rw [SixQubit.Orbit36MacWilliams.Aco_pair,
    SixQubit.Orbit36MacWilliams.Aco_pair] at h
  linarith

theorem AEnum_permAct (σ : Equiv.Perm (Fin 6)) (c d : SS.State 6 ℂ) (j : ℕ) :
    SixQubit.Orbit36Phase.AEnum (permAct σ c) (permAct σ d) j =
      SixQubit.Orbit36Phase.AEnum c d j := by
  apply AEnum_eq_of_Aco_eq
  have h := Aco_permAct σ ![c, d] j
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem AEnum_flipAct (f : SS.BitString 6) (c d : SS.State 6 ℂ) (j : ℕ) :
    SixQubit.Orbit36Phase.AEnum (flipAct f c) (flipAct f d) j =
      SixQubit.Orbit36Phase.AEnum c d j := by
  apply AEnum_eq_of_Aco_eq
  have h := Aco_flipAct f ![c, d] j
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem AEnum_phase (lc ld : ℂ) (hlc : Complex.normSq lc = 1)
    (hld : Complex.normSq ld = 1) (c d : SS.State 6 ℂ) (j : ℕ) :
    SixQubit.Orbit36Phase.AEnum (scal lc c) (scal ld d) j =
      SixQubit.Orbit36Phase.AEnum c d j := by
  apply AEnum_eq_of_Aco_eq
  have h := Aco_phase ![c, d] ![lc, ld] (by
    intro k
    fin_cases k
    · exact hlc
    · exact hld) j
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem AEnum_flip_permAct (σ : Equiv.Perm (Fin 6)) (f : SS.BitString 6)
    (c d : SS.State 6 ℂ) (j : ℕ) :
    SixQubit.Orbit36Phase.AEnum (flipAct f (permAct σ c))
        (flipAct f (permAct σ d)) j =
      SixQubit.Orbit36Phase.AEnum c d j := by
  rw [AEnum_flipAct, AEnum_permAct]

theorem AEnum_swap (c d : SS.State 6 ℂ) (j : ℕ) :
    SixQubit.Orbit36Phase.AEnum d c j = SixQubit.Orbit36Phase.AEnum c d j := by
  apply AEnum_eq_of_Aco_eq
  have h := Aco_swap ![c, d] true j
  simpa only [swapIdx, Matrix.cons_val_zero, Matrix.cons_val_one] using h

end

end SixQubit.CodeEquiv
