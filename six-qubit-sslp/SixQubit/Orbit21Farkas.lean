import Mathlib
import SixQubit.Orbit21Residual
import SixQubit.Orbit21Bound
import SixQubit.BEnumerator
import SixQubit.Pin

/-!
# Orbit 21: the exact Farkas expansion and lower bound

`Orbit21Residual` proves that the integral residual coefficient annihilates
every projector supported in the two orbit fibres.  Here the same coefficient
is expanded into complete MacWilliams, twisted-shadow, and manifest square
terms.  The label arithmetic stays over six-bit `Nat` masks, while the sums are
genuine sums of complex projector traces.
-/

namespace SixQubit.Orbit21Farkas

open SS.MacWilliams SS.ShadowTwisted SixQubit.Realize

/-- Decode a pair of six-bit masks as a Pauli label. -/
def ofMask (p : Nat × Nat) : SS.PauliString 6 := ⟨nbit p.1, nbit p.2⟩

def idMask : Nat × Nat := (0, 0)

/-- The exact commutation sign used by the generated coefficient. -/
def bsign (E : Nat × Nat) (x z : Nat) : Int :=
  Orbit21Coef.sgn (Orbit21Coef.pr E.1 E.2 x z)

/-- The exact twisted-shadow sign used by the generated coefficient. -/
def tsign (E : Nat × Nat) (x z : Nat) : Int :=
  Orbit21Coef.sgn
    (Orbit21Coef.pr E.1 E.2 x z + Orbit21Coef.wt x z)

/-- A left fold by addition is the initial value plus the mapped sum. -/
lemma foldl_add_eq (L : List α) (f : α → Int) (a : Int) :
    L.foldl (fun acc e => acc + f e) a = a + (L.map f).sum := by
  induction L generalizing a with
  | nil => simp
  | cons e L ih =>
      simp only [List.foldl, List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- The same coefficient as `Orbit21Coef.coef`, written with list sums so its
linear-functional expansion is transparent. -/
def icoef (x z : Nat) : Int :=
  (if Orbit21Coef.wt x z = 2 then 32 else 0)
  - (Orbit21Coef.bset.map fun E => 2 * bsign E x z).sum
  - (Orbit21Coef.tset.map fun E => 2 * tsign E x z).sum
  - (if Orbit21Coef.mem x z Orbit21Coef.r2set then 64 else 0)
  - (if Orbit21Coef.mem x z Orbit21Coef.r3set then 96 else 0)
  - (if Orbit21Coef.mem x z Orbit21Coef.r4set then 128 else 0)
  + (if Orbit21Coef.wt x z = 6 then 16 else 0)
  + (if Orbit21Coef.wt x z = 1 then 64 else 0)
  + (if Orbit21Coef.wt x z = 2 then 16 else 0)
  + (if Orbit21Coef.wt x z = 3 then 16 else 0)
  - 6 * bsign idMask x z
  + (Orbit21Coef.zset.map fun E => 2 * bsign E x z).sum
  - (if Orbit21Coef.mem x z Orbit21Coef.zset then 64 else 0)
  + (if x = 0 && z = 0 then 96 else 0)

/-- The list-sum and generated forms agree definitionally after the elementary
fold lemma; no enumeration is needed for this bridge. -/
theorem icoef_eq_coef (x z : Nat) :
    icoef x z = Orbit21Coef.coef x z := by
  unfold icoef Orbit21Coef.coef bsign tsign idMask
  rw [foldl_add_eq, foldl_add_eq, foldl_add_eq]
  simp only [zero_add]

set_option maxRecDepth 40000 in
lemma num_nbit_lt : ∀ m < 64, num (nbit m) = m := by decide

set_option maxRecDepth 40000 in
lemma wt_num : ∀ x z : SS.BitString 6,
    Orbit21Coef.wt (num x) (num z) =
      (⟨x, z⟩ : SS.PauliString 6).wt := by decide

lemma eps_real (x z : SS.BitString 6) :
    ((Orbit21Residual.eps x z : Int) : ℝ) = chi x z := by
  exact_mod_cast Orbit21Residual.eps_cast x z

lemma sgn_cast_pow (k : Nat) :
    ((Orbit21Coef.sgn k : Int) : ℝ) = (-1 : ℝ) ^ k := by
  rw [neg_one_pow_eq_pow_mod_two]
  unfold Orbit21Coef.sgn
  by_cases h : k % 2 = 0
  · rw [if_pos h, h]
    norm_num
  · have h1 : k % 2 = 1 := by omega
    rw [if_neg h, h1]
    norm_num

lemma sgn_add_cast (a b : Nat) :
    ((Orbit21Coef.sgn (a + b) : Int) : ℝ) =
      (Orbit21Coef.sgn a : Int) * (Orbit21Coef.sgn b : Int) := by
  rw [sgn_cast_pow, sgn_cast_pow, sgn_cast_pow, pow_add]

/-- One mask dot-product sign is the corresponding Walsh character. -/
lemma sgn_dot_eq_chi (m : Nat) (hm : m < 64) (x : SS.BitString 6) :
    ((Orbit21Coef.sgn (Orbit21Coef.pc (m &&& num x)) : Int) : ℝ) =
      chi x (nbit m) := by
  have h := eps_real x (nbit m)
  rw [Orbit21Residual.eps_num, num_nbit_lt m hm] at h
  rw [Nat.and_comm]
  exact h

/-- The mask commutation sign is the real complete-enumerator pairing sign. -/
lemma bsign_eq_pairSign (E : Nat × Nat) (hx : E.1 < 64) (hz : E.2 < 64)
    (x z : SS.BitString 6) :
    ((bsign E (num x) (num z) : Int) : ℝ) =
      pairSign (ofMask E) (⟨x, z⟩ : SS.PauliString 6) := by
  have hmod : Orbit21Coef.sgn
      (Orbit21Coef.pr E.1 E.2 (num x) (num z)) =
      Orbit21Coef.sgn
        (Orbit21Coef.pc (E.1 &&& num z) + Orbit21Coef.pc (E.2 &&& num x)) := by
    unfold Orbit21Coef.pr Orbit21Coef.sgn
    simp only [Nat.mod_mod]
  unfold bsign pairSign ofMask
  rw [hmod, sgn_add_cast,
    sgn_dot_eq_chi E.1 hx z, sgn_dot_eq_chi E.2 hz x]
  ring

/-- The mask shadow sign is the real alternating complete-shadow sign. -/
lemma tsign_eq_shadowSign (E : Nat × Nat) (hx : E.1 < 64) (hz : E.2 < 64)
    (x z : SS.BitString 6) :
    ((tsign E (num x) (num z) : Int) : ℝ) =
      (-1 : ℝ) ^ (⟨x, z⟩ : SS.PauliString 6).wt *
        pairSign (ofMask E) (⟨x, z⟩ : SS.PauliString 6) := by
  unfold tsign
  rw [sgn_add_cast]
  have hb := bsign_eq_pairSign E hx hz x z
  unfold bsign at hb
  rw [hb, sgn_cast_pow, wt_num]
  ring

noncomputable section

/-- Squared projector trace at a mask label. -/
def nval (psi : Fin 2 → SS.State 6 ℂ) (x z : Nat) : ℝ :=
  Complex.normSq (trProj psi (ofMask (x, z)))

/-- Sum a real mask coefficient against all 4096 squared traces. -/
def maskSum (psi : Fin 2 → SS.State 6 ℂ) (c : Nat → Nat → ℝ) : ℝ :=
  ∑ x : SS.BitString 6, ∑ z : SS.BitString 6,
    c (num x) (num z) * Complex.normSq (trProj psi ⟨x, z⟩)

/-- Weight-`j` complete A mass, in mask form. -/
def aRaw (psi : Fin 2 → SS.State 6 ℂ) (j : Nat) : ℝ :=
  maskSum psi fun x z => if Orbit21Coef.wt x z = j then 1 else 0

/-- Complete MacWilliams transform for one mask label. -/
def bRaw (psi : Fin 2 → SS.State 6 ℂ) (E : Nat × Nat) : ℝ :=
  maskSum psi fun x z => (bsign E x z : ℝ)

/-- Complete twisted-shadow transform for one mask label. -/
def tRaw (psi : Fin 2 → SS.State 6 ℂ) (E : Nat × Nat) : ℝ :=
  maskSum psi fun x z => (tsign E x z : ℝ)

/-- Mass selected by a finite mask list. -/
def rRaw (psi : Fin 2 → SS.State 6 ℂ) (L : List (Nat × Nat)) : ℝ :=
  maskSum psi fun x z => if Orbit21Coef.mem x z L then 1 else 0

/-- Mass of the identity label. -/
def iRaw (psi : Fin 2 → SS.State 6 ℂ) : ℝ :=
  maskSum psi fun x z => if x = 0 && z = 0 then 1 else 0

/-- Mass at one exact mask label. -/
def dRaw (psi : Fin 2 → SS.State 6 ℂ) (m k : Nat) : ℝ :=
  maskSum psi fun x z => if x = m && z = k then 1 else 0

/-- Sum of the complete transforms over a finite list of labels. -/
def bTotal (psi : Fin 2 → SS.State 6 ℂ) (L : List (Nat × Nat)) : ℝ :=
  (L.map (bRaw psi)).sum

/-- Sum of twisted-shadow transforms over a finite list of labels. -/
def tTotal (psi : Fin 2 → SS.State 6 ℂ) (L : List (Nat × Nat)) : ℝ :=
  (L.map (tRaw psi)).sum

/-- The manifestly nonnegative part of the certificate. -/
def positiveRhs (psi : Fin 2 → SS.State 6 ℂ) : ℝ :=
  2 * bTotal psi Orbit21Coef.bset
  + 2 * tTotal psi Orbit21Coef.tset
  + 64 * rRaw psi Orbit21Coef.r2set
  + 96 * rRaw psi Orbit21Coef.r3set
  + 128 * rRaw psi Orbit21Coef.r4set

/-- The generated residual, now as a real functional. -/
def residual (psi : Fin 2 → SS.State 6 ℂ) : ℝ :=
  maskSum psi fun x z => (Orbit21Coef.coef x z : ℝ)

lemma maskSum_add (psi : Fin 2 → SS.State 6 ℂ) (c d : Nat → Nat → ℝ) :
    maskSum psi (fun x z => c x z + d x z) = maskSum psi c + maskSum psi d := by
  unfold maskSum
  simp_rw [add_mul, Finset.sum_add_distrib]

lemma maskSum_sub (psi : Fin 2 → SS.State 6 ℂ) (c d : Nat → Nat → ℝ) :
    maskSum psi (fun x z => c x z - d x z) = maskSum psi c - maskSum psi d := by
  unfold maskSum
  simp_rw [sub_mul, Finset.sum_sub_distrib]

lemma maskSum_smul (psi : Fin 2 → SS.State 6 ℂ) (a : ℝ) (c : Nat → Nat → ℝ) :
    maskSum psi (fun x z => a * c x z) = a * maskSum psi c := by
  unfold maskSum
  simp_rw [mul_assoc, Finset.mul_sum]

/-- Move a finite label sum outside `maskSum`. -/
lemma maskSum_blist (psi : Fin 2 → SS.State 6 ℂ) (L : List (Nat × Nat)) :
    maskSum psi (fun x z => ((L.map fun E => bsign E x z).sum : Int)) =
      bTotal psi L := by
  induction L with
  | nil => simp [maskSum, bTotal]
  | cons E L ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, bTotal]
      rw [maskSum_add, ih]
      rfl

/-- Twisted-shadow analogue of `maskSum_blist`. -/
lemma maskSum_tlist (psi : Fin 2 → SS.State 6 ℂ) (L : List (Nat × Nat)) :
    maskSum psi (fun x z => ((L.map fun E => tsign E x z).sum : Int)) =
      tTotal psi L := by
  induction L with
  | nil => simp [maskSum, tTotal]
  | cons E L ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, tTotal]
      rw [maskSum_add, ih]
      rfl

/-- The mask residual is exactly the Pauli residual annihilated in
`Orbit21Residual`. -/
theorem residual_eq_pauli (psi : Fin 2 → SS.State 6 ℂ) :
    residual psi = ∑ P : SS.PauliString 6,
      SixQubit.Orbit21Bridge.cf P * Complex.normSq (trProj psi P) := by
  unfold residual maskSum SixQubit.Orbit21Bridge.cf
  rw [sum_pauli]

/-- Mask weight agrees with genuine Pauli weight, hence `aRaw` is `Aco`. -/
theorem aRaw_eq_Aco (psi : Fin 2 → SS.State 6 ℂ) (j : Nat) :
    aRaw psi j = Aco psi j := by
  unfold aRaw maskSum Aco
  rw [Finset.sum_filter, sum_pauli]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
  change (if Orbit21Coef.wt (num x) (num z) = j then 1 else 0) *
      Complex.normSq (trProj psi ⟨x, z⟩) =
    if (⟨x, z⟩ : SS.PauliString 6).wt = j then
      Complex.normSq (trProj psi ⟨x, z⟩) else 0
  rw [wt_num]
  by_cases h : (⟨x, z⟩ : SS.PauliString 6).wt = j
  · simp [h]
  · simp [h]

/-- Complete mask transform equals `64 * frob`. -/
theorem bRaw_eq_frob (psi : Fin 2 → SS.State 6 ℂ) (E : Nat × Nat)
    (hx : E.1 < 64) (hz : E.2 < 64) :
    bRaw psi E = 64 * frob psi (ofMask E) := by
  unfold bRaw maskSum
  simp_rw [bsign_eq_pairSign E hx hz]
  have h := pauli_duality psi (ofMask E)
  unfold pairSign ofMask at *
  calc
    ∑ x : SS.BitString 6, ∑ z : SS.BitString 6,
        (chi x (nbit E.2) * chi z (nbit E.1)) *
          Complex.normSq (trProj psi ⟨x, z⟩)
        = ∑ P : SS.PauliString 6,
            (chi P.x (nbit E.2) * chi P.z (nbit E.1)) *
              Complex.normSq (trProj psi P) :=
          (sum_pauli (fun P : SS.PauliString 6 =>
            (chi P.x (nbit E.2) * chi P.z (nbit E.1)) *
              Complex.normSq (trProj psi P))).symm
    _ = ∑ P : SS.PauliString 6,
          (chi (nbit E.1) P.z * chi (nbit E.2) P.x) *
            Complex.normSq (trProj psi P) := by
            refine Finset.sum_congr rfl (fun P _ => ?_)
            rw [chi_comm P.x, chi_comm P.z]
            ring
    _ = 64 * frob psi ⟨nbit E.1, nbit E.2⟩ := by norm_num at h ⊢; exact h

/-- Complete twisted mask transform is the kernel-proved nonnegative shadow
sum. -/
theorem tRaw_nonneg (psi : Fin 2 → SS.State 6 ℂ) (E : Nat × Nat)
    (hx : E.1 < 64) (hz : E.2 < 64) : 0 ≤ tRaw psi E := by
  have heq : tRaw psi E = ∑ P : SS.PauliString 6,
      (-1 : ℝ) ^ P.wt * pairSign (ofMask E) P *
        Complex.normSq (trProj psi P) := by
    unfold tRaw maskSum
    simp_rw [tsign_eq_shadowSign E hx hz]
    exact (sum_pauli (fun P : SS.PauliString 6 =>
      (-1 : ℝ) ^ P.wt * pairSign (ofMask E) P *
        Complex.normSq (trProj psi P))).symm
  rw [heq]
  exact altT_sum_nonneg psi (ofMask E)

theorem bRaw_nonneg (psi : Fin 2 → SS.State 6 ℂ) (E : Nat × Nat)
    (hx : E.1 < 64) (hz : E.2 < 64) : 0 ≤ bRaw psi E := by
  rw [bRaw_eq_frob psi E hx hz]
  exact mul_nonneg (by norm_num) (SixQubit.Orbit21Bound.frob_nonneg psi _)

theorem rRaw_nonneg (psi : Fin 2 → SS.State 6 ℂ) (L : List (Nat × Nat)) :
    0 ≤ rRaw psi L := by
  unfold rRaw maskSum
  refine Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun z _ => ?_))
  change 0 ≤ (if Orbit21Coef.mem (num x) (num z) L then 1 else 0) *
    Complex.normSq (trProj psi ⟨x, z⟩)
  by_cases h : Orbit21Coef.mem (num x) (num z) L = true
  · simp [h, Complex.normSq_nonneg]
  · have hf := Bool.eq_false_of_not_eq_true h
    simp [hf]

theorem iRaw_nonneg (psi : Fin 2 → SS.State 6 ℂ) : 0 ≤ iRaw psi := by
  unfold iRaw maskSum
  refine Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun z _ => ?_))
  change 0 ≤ (if num x = 0 && num z = 0 then 1 else 0) *
    Complex.normSq (trProj psi ⟨x, z⟩)
  by_cases h : (decide (num x = 0) && decide (num z = 0)) = true
  · simp [h, Complex.normSq_nonneg]
  · have hf := Bool.eq_false_of_not_eq_true h
    simp [hf]

lemma maskSum_congr (psi : Fin 2 → SS.State 6 ℂ) (c d : Nat → Nat → ℝ)
    (h : ∀ x z, c x z = d x z) : maskSum psi c = maskSum psi d := by
  unfold maskSum
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
  rw [h]

lemma cast_map_two_sum (L : List α) (f : α → Int) :
    (((L.map fun e => 2 * f e).sum : Int) : ℝ) =
      2 * (((L.map f).sum : Int) : ℝ) := by
  induction L with
  | nil => simp
  | cons e L ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul,
        Int.cast_ofNat]
      rw [ih]
      ring

lemma map_two_sum (L : List α) (f : α → Int) :
    (L.map fun e => 2 * f e).sum = 2 * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- Exact expansion of the generated coefficient as global mask
functionals. -/
theorem residual_expansion (psi : Fin 2 → SS.State 6 ℂ) :
    residual psi =
      32 * aRaw psi 2
      - 2 * bTotal psi Orbit21Coef.bset
      - 2 * tTotal psi Orbit21Coef.tset
      - 64 * rRaw psi Orbit21Coef.r2set
      - 96 * rRaw psi Orbit21Coef.r3set
      - 128 * rRaw psi Orbit21Coef.r4set
      + 16 * aRaw psi 6
      + 64 * aRaw psi 1
      + 16 * aRaw psi 2
      + 16 * aRaw psi 3
      - 6 * bRaw psi idMask
      + 2 * bTotal psi Orbit21Coef.zset
      - 64 * rRaw psi Orbit21Coef.zset
      + 96 * iRaw psi := by
  let A : Nat → Nat → Nat → ℝ := fun j x z =>
    if Orbit21Coef.wt x z = j then 1 else 0
  let B : List (Nat × Nat) → Nat → Nat → ℝ := fun L x z =>
    ((L.map fun E => bsign E x z).sum : Int)
  let T : List (Nat × Nat) → Nat → Nat → ℝ := fun L x z =>
    ((L.map fun E => tsign E x z).sum : Int)
  let R : List (Nat × Nat) → Nat → Nat → ℝ := fun L x z =>
    if Orbit21Coef.mem x z L then 1 else 0
  let I : Nat → Nat → ℝ := fun x z => if x = 0 && z = 0 then 1 else 0
  have hc : ∀ x z,
      (Orbit21Coef.coef x z : ℝ) =
        32 * A 2 x z
        - 2 * B Orbit21Coef.bset x z
        - 2 * T Orbit21Coef.tset x z
        - 64 * R Orbit21Coef.r2set x z
        - 96 * R Orbit21Coef.r3set x z
        - 128 * R Orbit21Coef.r4set x z
        + 16 * A 6 x z + 64 * A 1 x z
        + 16 * A 2 x z + 16 * A 3 x z
        - 6 * B [idMask] x z
        + 2 * B Orbit21Coef.zset x z
        - 64 * R Orbit21Coef.zset x z
        + 96 * I x z := by
    intro x z
    rw [← icoef_eq_coef]
    unfold icoef A B T R I
    rw [map_two_sum, map_two_sum, map_two_sum]
    push_cast
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, mul_ite]
    ring_nf
  calc
    residual psi = maskSum psi (fun x z => (Orbit21Coef.coef x z : ℝ)) := rfl
    _ = maskSum psi (fun x z =>
        32 * A 2 x z
        - 2 * B Orbit21Coef.bset x z
        - 2 * T Orbit21Coef.tset x z
        - 64 * R Orbit21Coef.r2set x z
        - 96 * R Orbit21Coef.r3set x z
        - 128 * R Orbit21Coef.r4set x z
        + 16 * A 6 x z + 64 * A 1 x z
        + 16 * A 2 x z + 16 * A 3 x z
        - 6 * B [idMask] x z
        + 2 * B Orbit21Coef.zset x z
        - 64 * R Orbit21Coef.zset x z
        + 96 * I x z) := maskSum_congr psi _ _ hc
    _ = 32 * maskSum psi (A 2)
        - 2 * maskSum psi (B Orbit21Coef.bset)
        - 2 * maskSum psi (T Orbit21Coef.tset)
        - 64 * maskSum psi (R Orbit21Coef.r2set)
        - 96 * maskSum psi (R Orbit21Coef.r3set)
        - 128 * maskSum psi (R Orbit21Coef.r4set)
        + 16 * maskSum psi (A 6) + 64 * maskSum psi (A 1)
        + 16 * maskSum psi (A 2) + 16 * maskSum psi (A 3)
        - 6 * maskSum psi (B [idMask])
        + 2 * maskSum psi (B Orbit21Coef.zset)
        - 64 * maskSum psi (R Orbit21Coef.zset)
        + 96 * maskSum psi I := by
          simp only [maskSum_add, maskSum_sub, maskSum_smul]
    _ = _ := by
      change 32 * aRaw psi 2
        - 2 * maskSum psi (B Orbit21Coef.bset)
        - 2 * maskSum psi (T Orbit21Coef.tset)
        - 64 * rRaw psi Orbit21Coef.r2set
        - 96 * rRaw psi Orbit21Coef.r3set
        - 128 * rRaw psi Orbit21Coef.r4set
        + 16 * aRaw psi 6 + 64 * aRaw psi 1
        + 16 * aRaw psi 2 + 16 * aRaw psi 3
        - 6 * maskSum psi (B [idMask])
        + 2 * maskSum psi (B Orbit21Coef.zset)
        - 64 * rRaw psi Orbit21Coef.zset
        + 96 * iRaw psi = _
      have hb := maskSum_blist psi Orbit21Coef.bset
      have ht := maskSum_tlist psi Orbit21Coef.tset
      have hi := maskSum_blist psi [idMask]
      have hz := maskSum_blist psi Orbit21Coef.zset
      change maskSum psi (B Orbit21Coef.bset) = _ at hb
      change maskSum psi (T Orbit21Coef.tset) = _ at ht
      change maskSum psi (B [idMask]) = _ at hi
      change maskSum psi (B Orbit21Coef.zset) = _ at hz
      simp only [bTotal, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero] at hi
      rw [hb, ht, hi, hz]

theorem bTotal_nonneg_of (psi : Fin 2 → SS.State 6 ℂ) (L : List (Nat × Nat))
    (h : ∀ E ∈ L, E.1 < 64 ∧ E.2 < 64) : 0 ≤ bTotal psi L := by
  unfold bTotal
  induction L with
  | nil => simp
  | cons E L ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_nonneg
      · exact bRaw_nonneg psi E (h E (by simp)).1 (h E (by simp)).2
      · apply ih
        intro F hF
        exact h F (by simp [hF])

theorem tTotal_nonneg_of (psi : Fin 2 → SS.State 6 ℂ) (L : List (Nat × Nat))
    (h : ∀ E ∈ L, E.1 < 64 ∧ E.2 < 64) : 0 ≤ tTotal psi L := by
  unfold tTotal
  induction L with
  | nil => simp
  | cons E L ih =>
      simp only [List.map_cons, List.sum_cons]
      apply add_nonneg
      · exact tRaw_nonneg psi E (h E (by simp)).1 (h E (by simp)).2
      · apply ih
        intro F hF
        exact h F (by simp [hF])

theorem bset_bounds : ∀ E ∈ Orbit21Coef.bset, E.1 < 64 ∧ E.2 < 64 := by
  intro E hE
  simp only [Orbit21Coef.bset, List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl | rfl <;> norm_num

set_option maxHeartbeats 1000000 in
theorem tset_bounds : ∀ E ∈ Orbit21Coef.tset, E.1 < 64 ∧ E.2 < 64 := by
  intro E hE
  simp only [Orbit21Coef.tset, List.mem_cons, List.not_mem_nil, or_false] at hE
  rcases hE with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num

theorem positiveRhs_nonneg (psi : Fin 2 → SS.State 6 ℂ) :
    0 ≤ positiveRhs psi := by
  have hb := bTotal_nonneg_of psi Orbit21Coef.bset bset_bounds
  have ht := tTotal_nonneg_of psi Orbit21Coef.tset tset_bounds
  have hr2 := rRaw_nonneg psi Orbit21Coef.r2set
  have hr3 := rRaw_nonneg psi Orbit21Coef.r3set
  have hr4 := rRaw_nonneg psi Orbit21Coef.r4set
  unfold positiveRhs
  nlinarith

set_option maxRecDepth 40000 in
@[simp] lemma num_eq_zero_iff (x : SS.BitString 6) :
    num x = 0 ↔ x = nbit 0 := by
  revert x
  decide

/-- The identity selector contains exactly the identity Pauli. -/
theorem iRaw_eq_nval (psi : Fin 2 → SS.State 6 ℂ) :
    iRaw psi = nval psi 0 0 := by
  classical
  unfold iRaw maskSum nval ofMask
  simp only [num_eq_zero_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [show (∑ x : SS.BitString 6, ∑ z : SS.BitString 6,
      (if x = nbit 0 ∧ z = nbit 0 then 1 else 0) *
        Complex.normSq (trProj psi ⟨x, z⟩)) =
      ∑ x : SS.BitString 6, ∑ z : SS.BitString 6,
        if x = nbit 0 then
          (if z = nbit 0 then Complex.normSq (trProj psi ⟨x, z⟩) else 0)
        else 0 by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
      by_cases hx : x = nbit 0 <;> by_cases hz : z = nbit 0 <;> simp [hx, hz]]
  simp

set_option maxRecDepth 40000 in
lemma num_eq_iff_nbit (x : SS.BitString 6) (m : Nat) (hm : m < 64) :
    num x = m ↔ x = nbit m := by
  constructor
  · intro h
    rw [← h, nbit_num]
  · intro h
    rw [h, num_nbit_lt m hm]

/-- A single mask selector contains exactly its decoded Pauli. -/
theorem dRaw_eq_nval (psi : Fin 2 → SS.State 6 ℂ) (m k : Nat)
    (hm : m < 64) (hk : k < 64) : dRaw psi m k = nval psi m k := by
  classical
  unfold dRaw maskSum nval ofMask
  simp only [num_eq_iff_nbit _ m hm, num_eq_iff_nbit _ k hk,
    Bool.and_eq_true, decide_eq_true_eq]
  rw [show (∑ x : SS.BitString 6, ∑ z : SS.BitString 6,
      (if x = nbit m ∧ z = nbit k then 1 else 0) *
        Complex.normSq (trProj psi ⟨x, z⟩)) =
      ∑ x : SS.BitString 6, ∑ z : SS.BitString 6,
        if x = nbit m then
          (if z = nbit k then Complex.normSq (trProj psi ⟨x, z⟩) else 0)
        else 0 by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z _ => ?_))
      by_cases hx : x = nbit m <;> by_cases hz : z = nbit k <;> simp [hx, hz]]
  simp

/-- The four-label membership selector used by the KL correction splits into
four disjoint point selectors. -/
lemma zset_selector (x z : Nat) :
    (if Orbit21Coef.mem x z Orbit21Coef.zset then (1 : ℝ) else 0) =
      (if x = 0 && z = 1 then 1 else 0)
      + (if x = 0 && z = 2 then 1 else 0)
      + (if x = 0 && z = 4 then 1 else 0)
      + (if x = 0 && z = 32 then 1 else 0) := by
  unfold Orbit21Coef.mem Orbit21Coef.zset
  simp only [List.contains_cons, List.contains_nil, Bool.or_false,
    beq_iff_eq, Bool.or_eq_true, Prod.mk.injEq,
    Bool.and_eq_true, decide_eq_true_eq]
  by_cases hx : x = 0
  · subst x
    by_cases h1 : z = 1
    · subst z; norm_num
    · by_cases h2 : z = 2
      · subst z; norm_num
      · by_cases h4 : z = 4
        · subst z; norm_num
        · by_cases h32 : z = 32
          · subst z; norm_num
          · simp [h1, h2, h4, h32]
  · simp [hx]

/-- The `zset` selector is the sum of its four exact label masses. -/
theorem rRaw_zset (psi : Fin 2 → SS.State 6 ℂ) :
    rRaw psi Orbit21Coef.zset =
      nval psi 0 1 + nval psi 0 2 + nval psi 0 4 + nval psi 0 32 := by
  unfold rRaw
  rw [maskSum_congr psi _
    (fun x z =>
      (if x = 0 && z = 1 then 1 else 0)
      + (if x = 0 && z = 2 then 1 else 0)
      + (if x = 0 && z = 4 then 1 else 0)
      + (if x = 0 && z = 32 then 1 else 0)) zset_selector]
  simp only [maskSum_add]
  change dRaw psi 0 1 + dRaw psi 0 2 + dRaw psi 0 4 + dRaw psi 0 32 = _
  rw [dRaw_eq_nval, dRaw_eq_nval, dRaw_eq_nval, dRaw_eq_nval] <;> norm_num

/-- A complete transform becomes thirty-two times its own squared trace under
the two-dimensional KL equation. -/
theorem bRaw_eq_32_nval_of_KL (psi : Fin 2 → SS.State 6 ℂ) (E : Nat × Nat)
    (hx : E.1 < 64) (hz : E.2 < 64)
    (hKL : SS.KLCondition psi (ofMask E)) :
    bRaw psi E = 32 * nval psi E.1 E.2 := by
  rw [bRaw_eq_frob psi E hx hz]
  have h := frob_of_KL psi (ofMask E) hKL
  unfold nval
  norm_num at h ⊢
  linarith

/-- The four weight-one KL corrections cancel exactly. -/
theorem z_correction_zero (psi : Fin 2 → SS.State 6 ℂ)
    (hd3 : SS.HasDistance psi 3) :
    2 * bTotal psi Orbit21Coef.zset -
      64 * rRaw psi Orbit21Coef.zset = 0 := by
  have hk1 : SS.KLCondition psi (ofMask (0, 1)) := hd3 _ (by decide)
  have hk2 : SS.KLCondition psi (ofMask (0, 2)) := hd3 _ (by decide)
  have hk4 : SS.KLCondition psi (ofMask (0, 4)) := hd3 _ (by decide)
  have hk32 : SS.KLCondition psi (ofMask (0, 32)) := hd3 _ (by decide)
  have h1 := bRaw_eq_32_nval_of_KL psi (0, 1) (by norm_num) (by norm_num) hk1
  have h2 := bRaw_eq_32_nval_of_KL psi (0, 2) (by norm_num) (by norm_num) hk2
  have h4 := bRaw_eq_32_nval_of_KL psi (0, 4) (by norm_num) (by norm_num) hk4
  have h32 := bRaw_eq_32_nval_of_KL psi (0, 32) (by norm_num) (by norm_num) hk32
  rw [rRaw_zset]
  simp only [bTotal, Orbit21Coef.zset, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [h1, h2, h4, h32]
  ring

/-- The identity-label squared trace is the weight-zero coefficient. -/
theorem nval_zero_eq_Aco_zero (psi : Fin 2 → SS.State 6 ℂ) :
    nval psi 0 0 = Aco psi 0 := by
  classical
  unfold nval ofMask Aco
  have hid : (⟨nbit 0, nbit 0⟩ : SS.PauliString 6) =
      (⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6) := by
    simp only [SS.PauliString.mk.injEq]
    constructor <;> funext i <;> fin_cases i <;> decide
  rw [hid]
  have hfil : (Finset.univ.filter (fun P : SS.PauliString 6 => P.wt = 0)) =
      {(⟨fun _ => false, fun _ => false⟩ : SS.PauliString 6)} := by
    ext P
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact SixQubit.Pin.wt_eq_zero_iff P
  rw [hfil, Finset.sum_singleton]

/-- Normalization fixes the identity mask mass to four. -/
theorem iRaw_eq_four (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1) : iRaw psi = 4 := by
  rw [iRaw_eq_nval, nval_zero_eq_Aco_zero]
  exact SixQubit.Pin.Aco_zero psi hnorm

/-- The identity complete-transform correction. -/
theorem identity_correction (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (hd3 : SS.HasDistance psi 3) :
    -6 * bRaw psi idMask + 96 * iRaw psi = -384 := by
  have hk : SS.KLCondition psi (ofMask idMask) := hd3 _ (by decide)
  have hb := bRaw_eq_32_nval_of_KL psi idMask (by norm_num [idMask])
    (by norm_num [idMask]) hk
  have hi := iRaw_eq_four psi hnorm
  have hn : nval psi 0 0 = 4 := by rw [← iRaw_eq_nval]; exact hi
  unfold idMask at hb
  norm_num at hb
  unfold idMask
  linarith [hi, hn, hb]

/-- The scalar MacWilliams normal form supplies the global-weight part of the
affine correction. -/
theorem weight_correction (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (hd3 : SS.HasDistance psi 3) :
    16 * aRaw psi 6 + 64 * aRaw psi 1 +
      16 * aRaw psi 2 + 16 * aRaw psi 3 = 256 := by
  have hA0 := SixQubit.Pin.Aco_zero psi hnorm
  obtain ⟨_, _, h6⟩ := macwilliams_six psi hd3 hA0
  rw [aRaw_eq_Aco, aRaw_eq_Aco, aRaw_eq_Aco, aRaw_eq_Aco]
  linarith

/-- All affine correction terms collapse to `-128`. -/
theorem affine_correction (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (hd3 : SS.HasDistance psi 3) :
    16 * aRaw psi 6 + 64 * aRaw psi 1 +
      16 * aRaw psi 2 + 16 * aRaw psi 3
      - 6 * bRaw psi idMask
      + 2 * bTotal psi Orbit21Coef.zset
      - 64 * rRaw psi Orbit21Coef.zset
      + 96 * iRaw psi = -128 := by
  have hw := weight_correction psi hnorm hd3
  have hi := identity_correction psi hnorm hd3
  have hz := z_correction_zero psi hd3
  linarith

/-- **The exact corrected certificate identity.** -/
theorem certificate_identity (psi : Fin 2 → SS.State 6 ℂ)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (hd3 : SS.HasDistance psi 3) :
    residual psi = 32 * (Aco psi 2 - 4) - positiveRhs psi := by
  have he := residual_expansion psi
  have ha := affine_correction psi hnorm hd3
  have h1 := aRaw_eq_Aco psi 1
  have h2 := aRaw_eq_Aco psi 2
  have h3 := aRaw_eq_Aco psi 3
  have h6 := aRaw_eq_Aco psi 6
  unfold positiveRhs
  linarith [he, ha, h1, h2, h3, h6]

/-- **Orbit 21's missing lower bound, for every full-fibre-supported code.** -/
theorem four_le_Aco_two (psi : Fin 2 → SS.State 6 ℂ)
    (h0 : ∀ s, SS.weight Orbit21Cert.av s ≠ 0 → psi 0 s = 0)
    (h1 : ∀ s, SS.weight Orbit21Cert.av s ≠ 2 → psi 1 s = 0)
    (hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1)
    (hd3 : SS.HasDistance psi 3) : 4 ≤ Aco psi 2 := by
  have hrp := SixQubit.Orbit21Residual.residual_vanishes psi h0 h1
  have hr : residual psi = 0 := by
    rw [residual_eq_pauli]
    exact hrp
  have hc := certificate_identity psi hnorm hd3
  have hp := positiveRhs_nonneg psi
  linarith

end

end SixQubit.Orbit21Farkas
