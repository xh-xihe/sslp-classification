import Mathlib
import MainTheory.PrimitiveMobius

/-!
# `six:eq:primitiveMobius`, in general

The proposition "Primitive sorted-vector count" states

  `P_6(q) = sum_{d | q} mu(d) * binom(q/d + 5, 6)`,

and `PrimitiveMobius` verifies it at the eight moduli the six-qubit reduction
uses, by evaluating both sides.  That file's own docstring names what it does
not do: "the general Mobius inversion.  That needs the counting identity
`binom(q+5,6) = sum_{d | q} P_6(q/d)`, hence a bijection between sorted vectors
of content `d` and primitive sorted vectors modulo `q/d`."

This file supplies exactly that, at every length `k` and every modulus, so the
proposition holds as stated rather than at a table of arguments.  Three steps:

* `sortedCount_eq_choose` -- the number of sorted vectors
  `0 <= a_1 <= ... <= a_k < m` is `binom(m + k - 1, k)`.  Proved by the
  multichoose recursion: splitting on `a_1 = 0` sends a sorted vector either to
  one of length `k - 1` over the same alphabet or, after subtracting one, to one
  of the same length over an alphabet smaller by one.
* `sum_primitiveCount_divisors` -- partitioning sorted vectors by their content
  `c = gcd(q, a_1, ..., a_k)` and dividing through by `c` gives
  `S_k(q) = sum_{d | q} P_k(d)`.
* `primitiveCount_eq_mobiusSum` -- Mobius inversion, from Mathlib's
  `ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq`.
-/

namespace MainTheory.SortedVectorMobius

open Finset

/-! ## Sorted vectors -/

instance decidableMonotoneFin (k m : ℕ) :
    DecidablePred fun f : Fin k → Fin m => Monotone f := fun f =>
  decidable_of_iff (∀ i j : Fin k, i ≤ j → f i ≤ f j)
    ⟨fun h _ _ hij => h _ _ hij, fun h _ _ hij => h hij⟩

/-- The sorted vectors `0 <= a_1 <= ... <= a_k < m` of the paper's
`eq:a-canonical`, as a finite set. -/
def sortedVec (k m : ℕ) : Finset (Fin k → Fin m) :=
  {f ∈ Finset.univ | Monotone f}

theorem mem_sortedVec {k m : ℕ} {f : Fin k → Fin m} :
    f ∈ sortedVec k m ↔ Monotone f := by
  simp [sortedVec]

/-- `S_k(m)`, the number of sorted vectors. -/
def sortedCount (k m : ℕ) : ℕ := (sortedVec k m).card

theorem sortedCount_zero_left (m : ℕ) : sortedCount 0 m = 1 := by
  have h : sortedVec 0 m = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro f _ i j _
    exact i.elim0
  rw [sortedCount, h, Finset.card_univ]
  simp

theorem sortedCount_zero_right (k : ℕ) : sortedCount (k + 1) 0 = 0 := by
  rw [sortedCount, Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro f _
  exact (f 0).elim0

/-! ### The multichoose recursion

Split the sorted vectors of length `k+1` over `{0, ..., m}` on whether the
first entry is zero.  Those that start at zero are a sorted vector of length
`k` with the leading zero prepended; those that do not have every entry at
least one, and subtracting one gives a sorted vector over `{0, ..., m-1}`. -/

private theorem card_zeroHead (k m : ℕ) :
    #{f ∈ sortedVec (k + 1) (m + 1) | f 0 = 0} = sortedCount k (m + 1) := by
  classical
  refine Finset.card_bij' (fun f _ => fun i : Fin k => f i.succ)
    (fun g _ => Fin.cons 0 g) ?_ ?_ ?_ ?_
  · intro f hf
    rw [mem_sortedVec]
    rw [Finset.mem_filter, mem_sortedVec] at hf
    intro i j hij
    exact hf.1 (Fin.succ_le_succ_iff.2 hij)
  · intro g hg
    rw [mem_sortedVec] at hg
    rw [Finset.mem_filter, mem_sortedVec]
    refine ⟨?_, by simp⟩
    intro i j hij
    revert hij
    induction i using Fin.cases with
    | zero =>
        intro _
        simp only [Fin.cons_zero]
        exact Fin.zero_le _
    | succ i' =>
        induction j using Fin.cases with
        | zero => intro hij; exact absurd hij (by simp [Fin.le_def])
        | succ j' =>
            intro hij
            simp only [Fin.cons_succ]
            exact hg (Fin.succ_le_succ_iff.1 hij)
  · intro f hf
    funext i
    induction i using Fin.cases with
    | zero =>
        simp only [Fin.cons_zero]
        rw [Finset.mem_filter] at hf
        exact hf.2.symm
    | succ i' => simp only [Fin.cons_succ]
  · intro g _
    funext i
    simp only [Fin.cons_succ]

private theorem card_nonzeroHead (k m : ℕ) :
    #{f ∈ sortedVec (k + 1) (m + 1) | ¬ f 0 = 0} = sortedCount (k + 1) m := by
  classical
  have key : ∀ f : Fin (k + 1) → Fin (m + 1), Monotone f → f 0 ≠ 0 →
      ∀ i, 1 ≤ (f i).val ∧ (f i).val - 1 < m := by
    intro f hmono hne i
    have h0 : (f 0).val ≠ 0 := by
      intro h
      exact hne (Fin.ext (by simpa using h))
    have hle : (f 0).val ≤ (f i).val := hmono (Fin.zero_le i)
    have hlt : (f i).val < m + 1 := (f i).isLt
    omega
  refine Finset.card_bij'
    (fun f hf => fun i : Fin (k + 1) =>
      (⟨(f i).val - 1, by
        rw [Finset.mem_filter, mem_sortedVec] at hf
        exact (key f hf.1 hf.2 i).2⟩ : Fin m))
    (fun g _ => fun i : Fin (k + 1) =>
      (⟨(g i).val + 1, by have := (g i).isLt; omega⟩ : Fin (m + 1)))
    ?_ ?_ ?_ ?_
  · intro f hf
    have hf' := hf
    rw [Finset.mem_filter, mem_sortedVec] at hf'
    rw [mem_sortedVec]
    intro i j hij
    have h1 := (key f hf'.1 hf'.2 i).1
    have h2 := (key f hf'.1 hf'.2 j).1
    have hle : (f i).val ≤ (f j).val := hf'.1 hij
    exact Fin.mk_le_mk.2 (by omega)
  · intro g hg
    rw [mem_sortedVec] at hg
    rw [Finset.mem_filter, mem_sortedVec]
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hle : (g i).val ≤ (g j).val := hg hij
      exact Fin.mk_le_mk.2 (by omega)
    · intro h
      have hval : (g 0).val + 1 = ((0 : Fin (m + 1)) : ℕ) := congrArg Fin.val h
      simp at hval
  · intro f hf
    have hf' := hf
    rw [Finset.mem_filter, mem_sortedVec] at hf'
    funext i
    have h1 := (key f hf'.1 hf'.2 i).1
    exact Fin.ext (by simp; omega)
  · intro g _
    funext i
    exact Fin.ext (by simp)

theorem sortedCount_succ_succ (k m : ℕ) :
    sortedCount (k + 1) (m + 1)
      = sortedCount k (m + 1) + sortedCount (k + 1) m := by
  classical
  rw [← card_zeroHead k m, ← card_nonzeroHead k m]
  exact (Finset.card_filter_add_card_filter_not (s := sortedVec (k + 1) (m + 1))
    (fun f => f 0 = 0)).symm

/-- **The number of sorted vectors is a multichoose coefficient.** -/
theorem sortedCount_eq_multichoose : ∀ m k : ℕ,
    sortedCount k m = Nat.multichoose m k
  | m, 0 => by rw [sortedCount_zero_left, Nat.multichoose_zero_right]
  | 0, (k + 1) => by rw [sortedCount_zero_right, Nat.multichoose_zero_succ]
  | (m + 1), (k + 1) => by
      rw [sortedCount_succ_succ, sortedCount_eq_multichoose (m + 1) k,
        sortedCount_eq_multichoose m (k + 1), Nat.multichoose_succ_succ,
        Nat.add_comm]
  termination_by m k => m + k

/-- **`binom(m + k - 1, k)`**, the paper's `binom(q/d + 5, 6)` at `k = 6`. -/
theorem sortedCount_eq_choose (k m : ℕ) :
    sortedCount k m = (m + k - 1).choose k := by
  rw [sortedCount_eq_multichoose, Nat.multichoose_eq]

/-! ## Content, and the primitive vectors -/

/-- `gcd(q, a_1, ..., a_k)`, the quantity `eq:primitive` sets to one. -/
def contentOf {k m : ℕ} (q : ℕ) (f : Fin k → Fin m) : ℕ :=
  Nat.gcd q (Finset.univ.gcd fun i => (f i).val)

theorem contentOf_dvd_left {k m : ℕ} (q : ℕ) (f : Fin k → Fin m) :
    contentOf q f ∣ q := Nat.gcd_dvd_left _ _

theorem contentOf_dvd_val {k m : ℕ} (q : ℕ) (f : Fin k → Fin m) (i : Fin k) :
    contentOf q f ∣ (f i).val :=
  dvd_trans (Nat.gcd_dvd_right _ _) (Finset.gcd_dvd (Finset.mem_univ i))

theorem contentOf_pos {k m : ℕ} {q : ℕ} (hq : 0 < q) (f : Fin k → Fin m) :
    0 < contentOf q f :=
  Nat.pos_of_ne_zero fun h => by
    have hz := Nat.eq_zero_of_gcd_eq_zero_left h
    omega

/-- The primitive sorted vectors of `six:eq:primitive`. -/
def primitiveVec (k q : ℕ) : Finset (Fin k → Fin q) :=
  {f ∈ sortedVec k q | contentOf q f = 1}

/-- `P_k(q)`. -/
def primitiveCount (k q : ℕ) : ℕ := (primitiveVec k q).card

/-! ### Dividing by the content

For each divisor `c` of `q`, the sorted vectors of content `c` are exactly the
`c`-fold multiples of the primitive sorted vectors modulo `q/c`. -/

private theorem gcd_div_content {k m : ℕ} (q : ℕ) (f : Fin k → Fin m)
    (hq : 0 < q) :
    (Finset.univ.gcd fun i => (f i).val / contentOf q f)
      = (Finset.univ.gcd fun i => (f i).val) / contentOf q f := by
  set c := contentOf q f with hc
  have hcpos : 0 < c := contentOf_pos hq f
  have hcG : c ∣ Finset.univ.gcd fun i => (f i).val := Nat.gcd_dvd_right _ _
  refine Nat.dvd_antisymm ?_ ?_
  · have hmul : c * (Finset.univ.gcd fun i => (f i).val / c)
        ∣ Finset.univ.gcd fun i => (f i).val := by
      refine Finset.dvd_gcd fun i _ => ?_
      obtain ⟨t, ht⟩ := contentOf_dvd_val q f i
      have hti : (f i).val / c = t := by
        rw [← hc] at ht
        rw [ht, Nat.mul_div_cancel_left _ hcpos]
      have hdt : (Finset.univ.gcd fun i => (f i).val / c) ∣ t := by
        rw [← hti]; exact Finset.gcd_dvd (Finset.mem_univ i)
      rw [← hc] at ht
      rw [ht]
      exact mul_dvd_mul_left c hdt
    exact (Nat.dvd_div_iff_mul_dvd hcG).2 hmul
  · refine Finset.dvd_gcd fun i _ => ?_
    have hGi : (Finset.univ.gcd fun i => (f i).val) ∣ (f i).val :=
      Finset.gcd_dvd (Finset.mem_univ i)
    obtain ⟨t, ht⟩ := hGi
    have hcGi : c ∣ (f i).val := contentOf_dvd_val q f i
    obtain ⟨u, hu⟩ := hcG
    refine ⟨t, ?_⟩
    rw [ht, hu]
    rw [Nat.mul_div_cancel_left _ hcpos, Nat.mul_assoc,
      Nat.mul_div_cancel_left _ hcpos]

private theorem card_contentFiber (k q c : ℕ) (hq : 0 < q) (hc : c ∣ q)
    (hcpos : 0 < c) :
    #{f ∈ sortedVec k q | contentOf q f = c} = primitiveCount k (q / c) := by
  classical
  refine Finset.card_bij'
    (fun f hf => fun i : Fin k =>
      (⟨(f i).val / c, by
        exact Nat.div_lt_div_of_lt_of_dvd hc (f i).isLt⟩ : Fin (q / c)))
    (fun g _ => fun i : Fin k =>
      (⟨c * (g i).val, by
        have h1 : (g i).val < q / c := (g i).isLt
        have h2 : c * (g i).val < c * (q / c) :=
          mul_lt_mul_of_pos_left h1 hcpos
        rwa [Nat.mul_div_cancel' hc] at h2⟩ : Fin q))
    ?_ ?_ ?_ ?_
  · intro f hf
    have hf' := hf
    rw [Finset.mem_filter, mem_sortedVec] at hf'
    rw [primitiveVec, Finset.mem_filter, mem_sortedVec]
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hle : (f i).val ≤ (f j).val := hf'.1 hij
      exact Fin.mk_le_mk.2 (Nat.div_le_div_right hle)
    · show Nat.gcd (q / c) (Finset.univ.gcd fun i => (f i).val / c) = 1
      have hrw : (fun i : Fin k => (f i).val / c)
          = (fun i : Fin k => (f i).val / contentOf q f) := by rw [hf'.2]
      rw [hrw, gcd_div_content q f hq, hf'.2]
      have hcop := Nat.coprime_div_gcd_div_gcd (m := q)
        (n := Finset.univ.gcd fun i => (f i).val)
        (by rw [← contentOf, hf'.2]; exact hcpos)
      rw [← contentOf, hf'.2] at hcop
      exact hcop
  · intro g hg
    rw [primitiveVec, Finset.mem_filter, mem_sortedVec] at hg
    rw [Finset.mem_filter, mem_sortedVec]
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hle : (g i).val ≤ (g j).val := hg.1 hij
      exact Fin.mk_le_mk.2 (Nat.mul_le_mul_left c hle)
    · show Nat.gcd q (Finset.univ.gcd fun i => c * (g i).val) = c
      have hgm : (Finset.univ.gcd fun i : Fin k => c * (g i).val)
          = c * Finset.univ.gcd (fun i : Fin k => (g i).val) := by
        simpa using Finset.gcd_mul_left (s := (Finset.univ : Finset (Fin k)))
          (f := fun i : Fin k => (g i).val) (a := c)
      have harith : ∀ Q G : ℕ, c ∣ Q → Nat.gcd (Q / c) G = 1 → Nat.gcd Q (c * G) = c := by
        intro Q G hdvd h1
        obtain ⟨t, rfl⟩ := hdvd
        rw [Nat.mul_div_cancel_left _ hcpos] at h1
        rw [Nat.gcd_mul_left, h1, Nat.mul_one]
      rw [hgm]
      exact harith q _ hc hg.2
  · intro f hf
    have hf' := hf
    rw [Finset.mem_filter, mem_sortedVec] at hf'
    funext i
    have hdv : c ∣ (f i).val := hf'.2 ▸ contentOf_dvd_val q f i
    exact Fin.ext (by simpa using Nat.mul_div_cancel' hdv)
  · intro g _
    funext i
    exact Fin.ext (by simp [Nat.mul_div_cancel_left _ hcpos])

/-- **The content decomposition**: every sorted vector is a unique multiple of
a primitive one. -/
theorem sum_primitiveCount_divisors (k : ℕ) {q : ℕ} (hq : 0 < q) :
    ∑ d ∈ q.divisors, primitiveCount k d = sortedCount k q := by
  classical
  have hmaps :
      ((sortedVec k q : Finset (Fin k → Fin q)) : Set (Fin k → Fin q)).MapsTo
        (fun f => contentOf q f) q.divisors := by
    intro f _
    simp only [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨contentOf_dvd_left q f, hq.ne'⟩
  have hsplit : sortedCount k q
      = ∑ c ∈ q.divisors, #{f ∈ sortedVec k q | contentOf q f = c} :=
    Finset.card_eq_sum_card_fiberwise hmaps
  rw [hsplit, ← Nat.sum_div_divisors q (fun d => primitiveCount k d)]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Nat.mem_divisors] at hc
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · exact absurd (Nat.eq_zero_of_zero_dvd hc.1) hq.ne'
    · exact h
  exact (card_contentFiber k q c hq hc.1 hcpos).symm

/-! ## Mobius inversion -/

open ArithmeticFunction in
/-- **`six:eq:primitiveMobius`, at every length and every modulus.** -/
theorem primitiveCount_eq_mobiusSum (k : ℕ) {q : ℕ} (hq : 0 < q) :
    (primitiveCount k q : ℤ)
      = ∑ d ∈ q.divisors, (moebius d : ℤ) * (sortedCount k (q / d) : ℤ) := by
  have hsum : ∀ m : ℕ, 0 < m →
      ∑ i ∈ m.divisors, (primitiveCount k i : ℤ) = (sortedCount k m : ℤ) := by
    intro m hm
    rw [← Nat.cast_sum, sum_primitiveCount_divisors k hm]
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
    (R := ℤ) (f := fun d => (primitiveCount k d : ℤ))
    (g := fun m => (sortedCount k m : ℤ))).1 hsum q hq
  rw [← hinv, ← Nat.map_div_right_divisors, Finset.sum_map]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp

/-- The paper's own display, with the binomial coefficient. -/
theorem primitiveCount_eq_mobiusChoose (k : ℕ) {q : ℕ} (hq : 0 < q) :
    (primitiveCount k q : ℤ)
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℤ)
          * (((q / d + k - 1).choose k : ℕ) : ℤ) := by
  rw [primitiveCount_eq_mobiusSum k hq]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sortedCount_eq_choose]


/-! ## The paper's own display

`PrimitiveMobius.mobiusCount` is the right-hand side of
`six:eq:primitiveMobius` at `k = 6`, evaluated there at the eight moduli the
six-qubit reduction uses.  With the inversion in hand it is now the theorem's
right-hand side at every modulus. -/

/-- **`six:eq:primitiveMobius`.** -/
theorem primitiveCount_six_eq_mobiusCount {q : ℕ} (hq : 0 < q) :
    (primitiveCount 6 q : ℤ) = MainTheory.PrimitiveMobius.mobiusCount q := by
  rw [primitiveCount_eq_mobiusSum 6 hq, MainTheory.PrimitiveMobius.mobiusCount]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [sortedCount_eq_choose]
  have hshift : ∀ x : ℕ, x + 6 - 1 = x + 5 := fun x => by omega
  rw [hshift]

/-- **The enumeration counts what the formula counts.**

`OuterEnumeration.primitiveAngles6` is the six-qubit outer loop's own list of
primitive sorted vectors, and `PrimitiveMobius.primitiveCount_eq_mobiusCount`
matches its length against the closed form at each modulus.  Composing that
with the inversion gives the two developments the same count at each of the
eight moduli -- a cardinality agreement, not a constructed bijection. -/
theorem primitiveAngles6_length_eq_primitiveCount :
    ∀ q ∈ ({2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ),
      (MainTheory.OuterEnumeration.primitiveAngles6 q).length = primitiveCount 6 q := by
  have h := MainTheory.PrimitiveMobius.primitiveCount_eq_mobiusCount
  intro q hq
  fin_cases hq <;>
    [ exact Nat.cast_injective (h.1.trans (primitiveCount_six_eq_mobiusCount (by norm_num)).symm);
      exact Nat.cast_injective (h.2.1.trans (primitiveCount_six_eq_mobiusCount (by norm_num)).symm);
      exact Nat.cast_injective (h.2.2.1.trans (primitiveCount_six_eq_mobiusCount (by norm_num)).symm);
      exact Nat.cast_injective (h.2.2.2.1.trans (primitiveCount_six_eq_mobiusCount (by norm_num)).symm);
      exact Nat.cast_injective (h.2.2.2.2.1.trans (primitiveCount_six_eq_mobiusCount (by norm_num)).symm);
      exact Nat.cast_injective (h.2.2.2.2.2.1.trans (primitiveCount_six_eq_mobiusCount (by norm_num)).symm);
      exact Nat.cast_injective (h.2.2.2.2.2.2.1.trans (primitiveCount_six_eq_mobiusCount (by norm_num)).symm);
      exact Nat.cast_injective (h.2.2.2.2.2.2.2.trans (primitiveCount_six_eq_mobiusCount (by norm_num)).symm) ]


/-! ## Two counts the six-qubit reduction states in closed form -/

/-- **`six:eq:starsbars`**: the stars-and-bars count of sorted six-vectors,
`#{0 <= a_1 <= ... <= a_6 < q} = binom(q + 5, 6)`.  This is the identity the
raw-count lemma behind `six:eq:13877` uses, and it holds at every `q`. -/
theorem sortedCount_six (q : ℕ) : sortedCount 6 q = (q + 5).choose 6 := by
  have hshift : ∀ x : ℕ, x + 6 - 1 = x + 5 := fun x => by omega
  rw [sortedCount_eq_choose, hshift]

/-- **`six:eq:qequalsm`**: the older `q = m` specialization keeps one logical
order per modulus, so it holds `sum_{q=2}^{9} binom(q+5,6) = 6434` records. -/
theorem sum_sortedCount_two_to_nine :
    ∑ q ∈ Finset.Icc 2 9, sortedCount 6 q = 6434 := by
  simp only [sortedCount_six]
  decide

end MainTheory.SortedVectorMobius
