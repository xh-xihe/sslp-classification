import MainTheory.PauliCategoryFourier
import SixQubit.ShadowTwisted

/-! # Physical Pauli labels and the category Fourier sum -/

namespace MainTheory.PhysicalPauliCategories

open MainTheory.PauliCategoryFourier SS.MacWilliams SS.ShadowTwisted
open scoped BigOperators

noncomputable section

def letter (b : Bool × Bool) : Letter :=
  ⟨(if b.1 then 1 else 0) + 2 * (if b.2 then 1 else 0), by
    rcases b with ⟨bx, bz⟩
    cases bx <;> cases bz <;> decide⟩

theorem letter_bits : ∀ b : Bool × Bool, (x (letter b), z (letter b)) = b := by
  decide +kernel

theorem bits_letter : ∀ p : Letter, letter (x p, z p) = p := by decide +kernel

def word (P : SS.PauliString n) : Fin n → Letter := fun i => letter (P.x i, P.z i)

def physical (p : Fin n → Letter) : SS.PauliString n := ⟨fun i => x (p i), fun i => z (p i)⟩

def wordEquiv (n : ℕ) : SS.PauliString n ≃ (Fin n → Letter) where
  toFun := word
  invFun := physical
  left_inv P := by
    cases P with
    | mk px pz =>
      have hx : (fun i => x (letter (px i, pz i))) = px := by
        funext i
        exact congrArg Prod.fst (letter_bits (px i, pz i))
      have hz : (fun i => z (letter (px i, pz i))) = pz := by
        funext i
        exact congrArg Prod.snd (letter_bits (px i, pz i))
      change SS.PauliString.mk _ _ = _
      dsimp only [word]
      rw [hx, hz]
  right_inv p := by
    funext i
    exact bits_letter (p i)

@[simp] theorem word_physical (p : Fin n → Letter) : word (physical p) = p :=
  (wordEquiv n).apply_symm_apply p

theorem pairSign_word (E P : SS.PauliString n) :
    pairSign E P = (totalSign (word E) (word P) : ℝ) := by
  unfold pairSign chi totalSign
  rw [← Finset.prod_mul_distrib, Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  have hE := letter_bits (E.x i, E.z i)
  have hP := letter_bits (P.x i, P.z i)
  have hxE := congrArg Prod.fst hE
  have hzE := congrArg Prod.snd hE
  have hxP := congrArg Prod.fst hP
  have hzP := congrArg Prod.snd hP
  dsimp only at hxE hzE hxP hzP
  unfold sign word
  rw [hxE, hzE, hxP, hzP]
  cases E.x i <;> cases E.z i <;> cases P.x i <;> cases P.z i <;> norm_num

def spectator (p : Letter) : ℕ := if p = 0 then 0 else 1

def categoryWord (p : Fin 6 → Letter) : ℕ × ℕ × ℕ :=
  (spectator (p 0), totalDegree (Fin.tail p))

def category (P : SS.PauliString 6) : ℕ × ℕ × ℕ := categoryWord (word P)

def spectatorFactor (p : Letter) (a : ℕ) : ℤ :=
  ∑ e : Letter, if spectator e = a then sign e p else 0

theorem spectatorFactor_formula (p : Letter) (a : Fin 2) :
    spectatorFactor p a = if a = 0 then 1 else if p = 0 then 3 else -1 := by
  fin_cases p <;> fin_cases a <;> norm_num [spectatorFactor, spectator, sign, x, z,
    Fin.sum_univ_succ]

theorem word_category_pairing_sum (p : Fin 6 → Letter) (c : ℕ × ℕ × ℕ) :
    (∑ e : Fin 6 → Letter, if categoryWord e = c then totalSign e p else 0) =
      spectatorFactor (p 0) c.1 * (∏ i : Fin 5, factor (p i.succ)) c.2 := by
  rw [← (Fin.consEquiv (fun _ : Fin 6 => Letter)).sum_comp]
  rw [Fintype.sum_prod_type]
  have hsplit (head : Letter) :
      (∑ tail : Fin 5 → Letter,
        if categoryWord (Fin.cons head tail) = c then
          totalSign (Fin.cons head tail) p else 0) =
      (if spectator head = c.1 then sign head (p 0) else 0) *
        (∏ i : Fin 5, factor (p i.succ)) c.2 := by
    have hc := category_pairing_sum (Fin.tail p) c.2
    simp only [Fin.tail] at hc
    rw [← hc]
    rcases c with ⟨a, jk⟩
    simp only [categoryWord, Fin.cons_zero, Fin.tail_cons,
      Prod.mk.injEq, totalSign, Fin.prod_univ_succ, Fin.cons_succ,
      Fin.tail, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tail _
    by_cases hh : spectator head = a <;>
      by_cases ht : totalDegree tail = jk <;> simp [hh, ht]
  change (∑ head : Letter, ∑ tail : Fin 5 → Letter,
    if categoryWord (Fin.cons head tail) = c then totalSign (Fin.cons head tail) p else 0) = _
  rw [Finset.sum_congr rfl (fun head _ => hsplit head), ← Finset.sum_mul]
  rfl

theorem physical_category_pairing_sum (P : SS.PauliString 6) (c : ℕ × ℕ × ℕ) :
    (∑ E : SS.PauliString 6, if category E = c then pairSign E P else 0) =
      (spectatorFactor (word P 0) c.1 : ℝ) *
        ((∏ i : Fin 5, factor (word P i.succ)) c.2 : ℝ) := by
  rw [← (wordEquiv 6).symm.sum_comp]
  change (∑ e : Fin 6 → Letter,
    if category (physical e) = c then pairSign (physical e) P else 0) = _
  simp only [category, pairSign_word, word_physical]
  have h := word_category_pairing_sum (word P) c
  exact_mod_cast h

def activeMask : SS.BitString 6 := fun i => i != 0

theorem active_parity_count : ∀ px : SS.BitString 6,
    SS.bdot activeMask px =
      ((Finset.univ.filter (fun i : Fin 5 => px i.succ = true)).card % 2 == 1) := by
  decide +kernel

theorem transverseCount_word_tail (P : SS.PauliString 6) :
    transverseCount (Fin.tail (word P)) =
      (Finset.univ.filter (fun i : Fin 5 => P.x i.succ = true)).card := by
  unfold transverseCount
  congr 1
  ext i
  have h := congrArg Prod.fst (letter_bits (P.x i.succ, P.z i.succ))
  dsimp only at h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.tail, word]
  rw [h]

theorem category_parity (P : SS.PauliString 6) :
    SS.bdot activeMask P.x = ((category P).2.2 % 2 == 1) := by
  rw [active_parity_count]
  unfold category categoryWord
  rw [totalDegree_counts, transverseCount_word_tail]

theorem weight_word (P : SS.PauliString n) :
    P.wt = ∑ i : Fin n, if word P i = 0 then 0 else 1 := by
  unfold SS.PauliString.wt
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  unfold word letter
  cases P.x i <;> cases P.z i <;> decide

theorem category_weight (P : SS.PauliString 6) :
    P.wt = (category P).1 + (category P).2.1 + (category P).2.2 := by
  rw [weight_word, Fin.sum_univ_succ]
  have hletter : ∀ p : Letter,
      (if p = 0 then 0 else 1) = (degree p).1 + (degree p).2 := by decide +kernel
  have htail : (∑ i : Fin 5, if word P i.succ = 0 then 0 else 1) =
      (totalDegree (Fin.tail (word P))).1 + (totalDegree (Fin.tail (word P))).2 := by
    simp_rw [hletter, Finset.sum_add_distrib]
    simp only [totalDegree, Fin.tail]
    change _ = (AddMonoidHom.fst ℕ ℕ) (∑ i : Fin 5, degree (word P i.succ)) +
      (AddMonoidHom.snd ℕ ℕ) (∑ i : Fin 5, degree (word P i.succ))
    rw [map_sum, map_sum]
    rfl
  rw [htail]
  unfold category categoryWord spectator
  dsimp only
  omega

end
end MainTheory.PhysicalPauliCategories
