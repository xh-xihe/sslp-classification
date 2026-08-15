import SS.QSqrt235i
import SS.FullKLEval
import DyadicLifts.KL
import DyadicLifts.Lift

/-!
# Embedding the exact field `ℚ(√2,√3,√5,i)` into `ℂ` (the Tier-3 bridge foundation)

The `SS` library verifies concrete distance-`3` codes by `native_decide` over the
*decidable* exact field `QSqrt235i = ℚ(√2,√3,√5,i)` (equality in `ℂ` is not
decidable, which is why the exact field exists).  To feed such a concrete code into
the abstract `DyadicLifts` ladder — whose `KLmat` lives over `ℂ` — we need a ring
embedding `QSqrt235i ↪ ℂ` along which `native_decide`'d equalities transport.

This module builds that embedding and proves it is compatible with `+`, `*`, `0`,
`1`, and complex conjugation.  The only non-trivial proof is multiplication
compatibility, discharged by `ring` modulo the square relations `√2²=2`, `√3²=3`,
`√5²=5`, `i²=-1`.
-/

open ComplexConjugate

namespace DyadicLifts

/-! ## The real square roots and their relations -/

noncomputable def s2 : ℂ := (Real.sqrt 2 : ℝ)
noncomputable def s3 : ℂ := (Real.sqrt 3 : ℝ)
noncomputable def s5 : ℂ := (Real.sqrt 5 : ℝ)

theorem s2_sq : s2 ^ 2 = 2 := by rw [s2, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
theorem s3_sq : s3 ^ 2 = 3 := by rw [s3, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
theorem s5_sq : s5 ^ 2 = 5 := by rw [s5, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

@[simp] theorem conj_s2 : conj s2 = s2 := by rw [s2]; exact Complex.conj_ofReal _
@[simp] theorem conj_s3 : conj s3 = s3 := by rw [s3]; exact Complex.conj_ofReal _
@[simp] theorem conj_s5 : conj s5 = s5 := by rw [s5]; exact Complex.conj_ofReal _

/-! ## The embedding `ℚ(√2,√3,i) ↪ ℂ` -/

open SS

/-- Embed `ℚ(√2,√3,i)` into `ℂ` (representing `√6` as `s2·s3`). -/
noncomputable def ιC23 (x : QSqrt23i) : ℂ :=
  ((x.re₀ : ℂ) + (x.re₁ : ℂ) * s2 + (x.re₂ : ℂ) * s3 + (x.re₃ : ℂ) * (s2 * s3))
  + ((x.im₀ : ℂ) + (x.im₁ : ℂ) * s2 + (x.im₂ : ℂ) * s3 + (x.im₃ : ℂ) * (s2 * s3)) * Complex.I

@[simp] theorem ιC23_zero : ιC23 0 = 0 := by
  show ιC23 QSqrt23i.zero = 0; simp [ιC23, QSqrt23i.zero]

@[simp] theorem ιC23_one : ιC23 1 = 1 := by
  show ιC23 QSqrt23i.one = 1; simp [ιC23, QSqrt23i.one]

theorem ιC23_add (x y : QSqrt23i) : ιC23 (x + y) = ιC23 x + ιC23 y := by
  show ιC23 (QSqrt23i.add x y) = ιC23 x + ιC23 y
  simp only [ιC23, QSqrt23i.add]; push_cast; ring

theorem ιC23_qsmul (q : ℚ) (x : QSqrt23i) : ιC23 (q • x) = (q : ℂ) * ιC23 x := by
  show ιC23 (QSqrt23i.smul q x) = (q : ℂ) * ιC23 x
  simp only [ιC23, QSqrt23i.smul]; push_cast; ring

theorem ιC23_mul (x y : QSqrt23i) : ιC23 (x * y) = ιC23 x * ιC23 y := by
  show ιC23 (QSqrt23i.mul x y) = ιC23 x * ιC23 y
  simp only [ιC23, QSqrt23i.mul, QSqrt23i.mulReal]
  push_cast
  ring_nf
  rw [Complex.I_sq, s2_sq, s3_sq]
  ring

theorem ιC23_conj (x : QSqrt23i) : ιC23 (QSqrt23i.conj x) = conj (ιC23 x) := by
  simp only [ιC23, QSqrt23i.conj]
  simp only [map_add, map_mul, map_ratCast, Complex.conj_I, conj_s2, conj_s3]
  push_cast
  ring

/-! ## The embedding `ℚ(√2,√3,√5,i) ↪ ℂ` -/

/-- Embed `ℚ(√2,√3,√5,i)` into `ℂ` via `⟨u,v⟩ ↦ ιC23 u + ιC23 v · √5`. -/
noncomputable def ιK (x : QSqrt235i) : ℂ := ιC23 x.u + ιC23 x.v * s5

@[simp] theorem ιK_zero : ιK 0 = 0 := by
  show ιK QSqrt235i.zero = 0; simp [ιK, QSqrt235i.zero]

@[simp] theorem ιK_one : ιK 1 = 1 := by
  show ιK QSqrt235i.one = 1; simp [ιK, QSqrt235i.one]

theorem ιK_add (x y : QSqrt235i) : ιK (x + y) = ιK x + ιK y := by
  show ιK (QSqrt235i.add x y) = ιK x + ιK y
  simp only [ιK, QSqrt235i.add, ιC23_add]; ring

theorem ιK_mul (x y : QSqrt235i) : ιK (x * y) = ιK x * ιK y := by
  show ιK (QSqrt235i.mul x y) = ιK x * ιK y
  simp only [ιK, QSqrt235i.mul, ιC23_add, ιC23_mul, ιC23_qsmul]
  ring_nf
  rw [s5_sq]

theorem ιK_conj (x : QSqrt235i) : ιK (QSqrt235i.conj x) = conj (ιK x) := by
  simp only [ιK, QSqrt235i.conj, ιC23_conj, map_add, map_mul, conj_s5]

@[simp] theorem ιC23_neg (x : QSqrt23i) : ιC23 (-x) = -ιC23 x := by
  show ιC23 (QSqrt23i.neg x) = -ιC23 x
  simp only [ιC23, QSqrt23i.neg]; push_cast; ring

@[simp] theorem ιK_neg (x : QSqrt235i) : ιK (-x) = -ιK x := by
  show ιK (QSqrt235i.neg x) = -ιK x
  simp only [ιK, QSqrt235i.neg, ιC23_neg]; ring

@[simp] theorem ιK_I : ιK QSqrt235i.I = Complex.I := by
  show ιC23 QSqrt23i.I + ιC23 0 * s5 = Complex.I
  rw [ιC23_zero]; simp [ιC23, QSqrt23i.I]

/-! ## The per-qubit Pauli matrix element over the exact field -/

/-- The single-qubit Pauli matrix element with values in `QSqrt235i` (mirrors `sqME`). -/
def sqMEK : SQ → Bool → Bool → QSqrt235i
  | SQ.I, a, b => if a = b then 1 else 0
  | SQ.X, a, b => if a = b then 0 else 1
  | SQ.Z, a, b => if a = b then (if b then -1 else 1) else 0
  | SQ.Y, a, b => if a = b then 0 else (if b then -QSqrt235i.I else QSqrt235i.I)

/-- The per-qubit bridge: `ιK` sends the exact-field matrix element to the `ℂ` one. -/
theorem ιK_sqMEK (P : SQ) (a b : Bool) : ιK (sqMEK P a b) = sqME P a b := by
  cases P <;> cases a <;> cases b <;>
    simp [sqMEK, sqME, ιK_neg, ιK_I, ιK_one, ιK_zero]

/-! ## `ιK` pushes through list folds (sum and product) -/

theorem ιK_listSum {ι : Type*} (l : List ι) (f : ι → QSqrt235i) :
    ιK (l.foldr (fun i acc => f i + acc) 0) = l.foldr (fun i acc => ιK (f i) + acc) 0 := by
  induction l with
  | nil => simp [ιK_zero]
  | cons a l ih => simp only [List.foldr_cons]; rw [ιK_add, ih]

theorem ιK_listProd {ι : Type*} (l : List ι) (f : ι → QSqrt235i) :
    ιK (l.foldr (fun i acc => f i * acc) 1) = l.foldr (fun i acc => ιK (f i) * acc) 1 := by
  induction l with
  | nil => simp [ιK_one]
  | cons a l ih => simp only [List.foldr_cons]; rw [ιK_mul, ih]

/-! ## `foldr` over `finRange`/`toList` equals `Finset.prod`/`Finset.sum` (over `ℂ`) -/

theorem foldr_finRange_mul {n : ℕ} (g : Fin n → ℂ) :
    (List.finRange n).foldr (fun i acc => g i * acc) 1 = ∏ i, g i := by
  rw [← List.prod_ofFn, List.ofFn_eq_map, List.prod_eq_foldr, List.foldr_map]

theorem foldr_toList_add {α : Type*} [Fintype α] (g : α → ℂ) :
    (Finset.univ.toList).foldr (fun i acc => g i + acc) 0 = ∑ i, g i := by
  rw [← Finset.sum_map_toList, List.sum_eq_foldr, List.foldr_map]

/-! ## The Pauli matrix element over the exact field, and its bridge -/

variable {n : ℕ}

/-- `pauliME` over the exact field `QSqrt235i` (a `foldr` product, no `CommMonoid` needed). -/
def pauliMEK (P : Fin n → SQ) (s t : BitString n) : QSqrt235i :=
  (List.finRange n).foldr (fun i acc => sqMEK (P i) (s i) (t i) * acc) 1

/-- **Bridge for the Pauli matrix element:** `ιK (pauliMEK P s t) = pauliME P s t`. -/
theorem ιK_pauliMEK (P : Fin n → SQ) (s t : BitString n) :
    ιK (pauliMEK P s t) = pauliME P s t := by
  rw [pauliMEK, ιK_listProd]
  simp only [ιK_sqMEK]
  rw [foldr_finRange_mul]
  rfl

/-! ## The Knill–Laflamme matrix element over the exact field, and the bridge to `KLmat` -/

open SS (foldSum)

/-- `ιK` pushes through the computable `foldSum` (`Finset.fold`) onto a `Finset.sum` over `ℂ`. -/
theorem ιK_foldSum (S : Finset (BitString n)) (f : BitString n → QSqrt235i) :
    ιK (foldSum S f) = ∑ s ∈ S, ιK (f s) := by
  classical
  induction S using Finset.induction with
  | empty => simp only [foldSum, Finset.fold_empty]; exact ιK_zero
  | @insert a S ha ih =>
      have hstep : foldSum (insert a S) f = QSqrt235i.add (f a) (foldSum S f) := by
        rw [foldSum, Finset.fold_insert ha]; rfl
      rw [hstep, Finset.sum_insert ha, ← ih]
      exact ιK_add _ _

/-- The KL matrix element `⟨ψ₀|P|ψ₁⟩` over the exact field, summed over a **support set**
`S` (computable; `S` must contain the supports of both codewords).  Restricting to `S`
instead of all of `BitString n` is what makes `native_decide` feasible. -/
def melK (S : Finset (BitString n)) (ψ0K : BitString n → QSqrt235i) (P : Fin n → SQ)
    (ψ1K : BitString n → QSqrt235i) : QSqrt235i :=
  foldSum S (fun s => QSqrt235i.conj (ψ0K s) * foldSum S (fun t => pauliMEK P s t * ψ1K t))

/-- **The matrix-element bridge.** If both codewords vanish off `S`, the support-restricted
exact-field `melK` over `S` maps to the full `ℂ` matrix element `mel`. -/
theorem ιK_melK {S : Finset (BitString n)} {ψ0K ψ1K : BitString n → QSqrt235i} (P : Fin n → SQ)
    (h0 : ∀ s, s ∉ S → ψ0K s = 0) (h1 : ∀ s, s ∉ S → ψ1K s = 0) :
    ιK (melK S ψ0K P ψ1K) = mel (fun s => ιK (ψ0K s)) P (fun s => ιK (ψ1K s)) := by
  rw [melK, ιK_foldSum]
  simp only [ιK_mul, ιK_conj, ιK_foldSum, ιK_pauliMEK]
  simp only [mel, inn, papply]
  have hinner : ∀ s, (∑ t ∈ S, pauliME P s t * ιK (ψ1K t)) = ∑ t, pauliME P s t * ιK (ψ1K t) :=
    fun s => Finset.sum_subset (Finset.subset_univ S)
      (fun t _ ht => by simp [h1 t ht, ιK_zero])
  simp only [hinner]
  exact Finset.sum_subset (Finset.subset_univ S)
    (fun s _ hs => by simp [h0 s hs, ιK_zero])

/-- The Knill–Laflamme predicate over the exact field (support `S`) — decidable. -/
def KLmatK (S : Finset (BitString n)) (ψ0K ψ1K : BitString n → QSqrt235i) : Prop :=
  ∀ P : Fin n → SQ, pauliWt P ≤ 2 →
    melK S ψ0K P ψ1K = 0 ∧ melK S ψ1K P ψ0K = 0 ∧ melK S ψ0K P ψ0K = melK S ψ1K P ψ1K

instance (S : Finset (BitString n)) (ψ0K ψ1K : BitString n → QSqrt235i) :
    Decidable (KLmatK S ψ0K ψ1K) := by unfold KLmatK; infer_instance

/-- **The Tier-3 bridge.** If both codewords vanish off the support `S` and the exact-field
KL conditions hold there (checkable by `native_decide`), then the `ℂ` codewords
`ιK∘ψ₀K`, `ιK∘ψ₁K` satisfy `KLmat`. -/
theorem KLmat_of_KLmatK {S : Finset (BitString n)} {ψ0K ψ1K : BitString n → QSqrt235i}
    (h0 : ∀ s, s ∉ S → ψ0K s = 0) (h1 : ∀ s, s ∉ S → ψ1K s = 0)
    (h : KLmatK S ψ0K ψ1K) : KLmat (fun s => ιK (ψ0K s)) (fun s => ιK (ψ1K s)) := by
  intro P hP
  obtain ⟨h1', h2', h3'⟩ := h P hP
  refine ⟨?_, ?_, ?_⟩
  · rw [← ιK_melK P h0 h1, h1', ιK_zero]
  · rw [← ιK_melK P h1 h0, h2', ιK_zero]
  · rw [← ιK_melK P h0 h0, ← ιK_melK P h1 h1, h3']

/-! ## The dyadic Bell lift over the exact field, and its bridge -/

theorem isqrt2_eq_inv : isqrt2 = s2⁻¹ := by
  simp only [isqrt2, s2, Complex.ofReal_inv]

/-- `1/√2 = (√2)/2` as an element of the exact field. -/
def isqrt2K : QSqrt235i := ⟨⟨0, 1/2, 0, 0, 0, 0, 0, 0⟩, 0⟩

theorem ιK_isqrt2K : ιK isqrt2K = isqrt2 := by
  have hs2 : s2 ≠ 0 := fun h => by have h2 := s2_sq; rw [h] at h2; norm_num at h2
  have hcomp : ιK isqrt2K = s2 / 2 := by
    show ιC23 ⟨0, 1/2, 0, 0, 0, 0, 0, 0⟩ + ιC23 0 * s5 = s2 / 2
    rw [ιC23_zero, zero_mul, add_zero]
    simp only [ιC23]; push_cast; ring
  rw [isqrt2_eq_inv, hcomp]
  field_simp
  linear_combination s2_sq

/-- The Bell parity flag over the exact field. -/
def bflagK (p : Bool) (uv : BitString 2) : QSqrt235i :=
  isqrt2K * ((if uv = bket1 p then 1 else 0) + (if uv = bket2 p then 1 else 0))

theorem ιK_bflagK (p : Bool) (uv : BitString 2) : ιK (bflagK p uv) = bflag p uv := by
  simp only [bflagK, ιK_mul, ιK_isqrt2K, ιK_add, apply_ite ιK, ιK_one, ιK_zero,
    bflag, Pi.smul_apply, Pi.add_apply, ket_apply, smul_eq_mul]

variable {n : ℕ}

/-- The dyadic Bell lift over the exact field. -/
def liftVecK (m : ℕ) (a : Fin n → ℕ) (k : Bool) (ψK : BitString n → QSqrt235i) :
    BitString (n + 2) → QSqrt235i :=
  fun w => ψK (bleft w) * bflagK (xor (hibit m a (bleft w)) k) (bright w)

/-- **The lift bridge:** the dyadic Bell lift commutes with the embedding `ιK`. -/
theorem liftVec_bridge (m : ℕ) (a : Fin n → ℕ) (k : Bool) (ψK : BitString n → QSqrt235i) :
    liftVec m a k (fun s => ιK (ψK s)) = fun w => ιK (liftVecK m a k ψK w) := by
  funext w
  simp only [liftVec, liftVecK, ιK_mul, ιK_bflagK]

end DyadicLifts
