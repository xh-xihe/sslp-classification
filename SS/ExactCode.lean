import SS.ExactAmplitude

/-! Generic exact-amplitude certificates for supplied finite codes.
Finite integer checks are transported to the existing complex Hilbert/KL semantics.
No canonical code theorem is used. -/

namespace SS.ExactCode
open SS.ExactAmplitude
open scoped BigOperators
variable {n K : Nat}

/-- One term of a matrix-element sum: `(-1)^{z.s} conj (cj (s xor x)) * ck s`. -/
def zterm (cj ck : SS.BitString n → ZQ) (x z s : SS.BitString n) : ZQ :=
  ZQ.signMul (SS.bdot z s) (ZQ.mul (ZQ.conj (cj (SS.bxor s x))) (ck s))

/-- Exact sum of a `ZQ`-valued function over a list of bitstrings. -/
def zsum (L : List (SS.BitString n)) (f : SS.BitString n → ZQ) : ZQ :=
  (L.map f).foldr ZQ.add ZQ.zero

/-- The exact matrix element `<psi_j| P(x,z) |psi_k>` without the `i^{#Y}`
prefactor; `Lk` is a support list for `ck`. -/
def zmat (cj ck : SS.BitString n → ZQ) (Lk : List (SS.BitString n))
    (x z : SS.BitString n) : ZQ :=
  zsum Lk (zterm cj ck x z)


noncomputable section

def stC (sc : Complex) (c : SS.BitString n -> ZQ) : SS.State n Complex := fun s => sc * toC (c s)

variable (sc : Complex)

/-- `toC` turns a `zsum` into an ordinary sum over the list. -/
lemma toC_zsum (L : List (SS.BitString n)) (f : SS.BitString n → ZQ) :
    toC (zsum L f) = (L.map (fun s => toC (f s))).sum := by
  unfold zsum
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.foldr_cons, List.sum_cons, toC_add, ih]

lemma zterm_eq_zero {cj ck : SS.BitString n → ZQ} {x z s : SS.BitString n}
    (h : ck s = ZQ.zero) : zterm cj ck x z s = ZQ.zero := by
  unfold zterm
  rw [h, ZQ.mul_zero_right, ZQ.signMul_zero]

/-- **The exact sums are the true Knill--Laflamme matrix elements.** -/
theorem matElt_eq (cj ck : SS.BitString n → ZQ) (Lk : List (SS.BitString n))
    (hnd : Lk.Nodup) (hk : ∀ s, s ∉ Lk → ck s = ZQ.zero) (P : SS.PauliString n) :
    SS.innerC (stC sc cj) (SS.pauliAct P (stC sc ck))
      = star sc * sc * (Complex.I ^ P.numY) * toC (zmat cj ck Lk P.x P.z) := by
  classical
  have hcong : ∀ s : SS.BitString n,
      SS.signC (SS.bdot P.z s) (star (stC sc cj (SS.bxor s P.x)) * stC sc ck s)
        = star sc * sc * toC (zterm cj ck P.x P.z s) := by
    intro s
    unfold zterm stC
    rw [toC_signMul, toC_mul, toC_conj]
    cases SS.bdot P.z s <;>
      simp only [SS.signC_true, SS.signC_false, star_mul'] <;> ring
  have hsub : ∑ s : SS.BitString n, toC (zterm cj ck P.x P.z s)
      = ∑ s ∈ Lk.toFinset, toC (zterm cj ck P.x P.z s) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro s _ hs
    rw [zterm_eq_zero (hk s (by simpa using hs)), toC_zero]
  have hkey : ∑ s : SS.BitString n,
      SS.signC (SS.bdot P.z s) (star (stC sc cj (SS.bxor s P.x)) * stC sc ck s)
        = star sc * sc * toC (zmat cj ck Lk P.x P.z) := by
    rw [Finset.sum_congr rfl (fun s _ => hcong s), ← Finset.mul_sum, hsub,
      List.sum_toFinset _ hnd, ← toC_zsum, zmat]
  rw [SS.innerC_pauliAct, hkey]
  ring

theorem distance_of_checks (c : Fin K → SS.BitString n → ZQ)
    (L : Fin K → List (SS.BitString n)) (base : Fin K) (d : Nat)
    (hnd : ∀ j, (L j).Nodup) (hs : ∀ j s, s ∉ L j → c j s = ZQ.zero)
    (hc : ∀ P : SS.PauliString n, P.wt ≤ d - 1 → ∀ j k,
      zmat (c j) (c k) (L k) P.x P.z =
        if j = k then zmat (c base) (c base) (L base) P.x P.z else ZQ.zero) :
    SS.HasDistance (fun j => stC sc (c j)) d := by
  intro P hw
  refine ⟨star sc * sc * Complex.I ^ P.numY *
    toC (zmat (c base) (c base) (L base) P.x P.z), ?_⟩
  intro j k
  rw [matElt_eq sc (c j) (c k) (L k) (hnd k) (hs k) P, hc P hw j k]
  split_ifs <;> simp

/-- Common normalization scale, interpreted in the actual complex numbers. -/
def scale (D : Nat) : ℂ := ((Real.sqrt (D : ℝ) : ℝ) : ℂ)⁻¹

lemma scale_sq (D : Nat) : star (scale D) * scale D = (D : ℂ)⁻¹ := by
  have hs : star (scale D) = scale D := by simp [scale]
  rw [hs, scale, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg D)]
  simp

lemma identity_action (phi : SS.State n ℂ) :
    SS.pauliAct (⟨fun _ => false, fun _ => false⟩ : SS.PauliString n) phi = phi := by
  funext t
  simp [SS.pauliAct, SS.PauliString.numY, SS.bdot]

theorem orthonormal_of_checks (D : Nat) (hD : 0 < D)
    (c : Fin K → SS.BitString n → ZQ) (L : Fin K → List (SS.BitString n))
    (hnd : ∀ j, (L j).Nodup) (hs : ∀ j s, s ∉ L j → c j s = ZQ.zero)
    (hc : ∀ j k, zmat (c j) (c k) (L k) (fun _ => false) (fun _ => false) =
      if j = k then z8 (Int.ofNat D) 0 0 0 0 0 0 0 else ZQ.zero) :
    ∀ j k, SS.innerC (stC (scale D) (c j)) (stC (scale D) (c k)) = if j = k then 1 else 0 := by
  intro j k
  have h := matElt_eq (scale D) (c j) (c k) (L k) (hnd k) (hs k)
    (⟨fun _ => false, fun _ => false⟩ : SS.PauliString n)
  rw [identity_action] at h
  rw [h]
  simp only [SS.PauliString.numY, Bool.false_and, Bool.false_eq_true, Finset.filter_false,
    Finset.card_empty, pow_zero, mul_one]
  rw [hc, scale_sq]
  have hn : (D : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  split_ifs <;> simp [toC_intCast, hn]

end

/-- Natural exponents avoid embedding roots of unity in the amplitude ring. -/
def exponent (a : Fin n → Nat) (s : SS.BitString n) : Nat := ∑ j, if s j then a j else 0

noncomputable section

def physicalGate (zeta : ℂ) (a : Fin n → Nat) (psi : SS.State n ℂ) : SS.State n ℂ :=
  fun s => (∏ j, zeta ^ (if s j then a j else 0)) * psi s

theorem physical_word (zeta : ℂ) (q : Nat) (hz : zeta ^ q = 1)
    (a : Fin n → Nat) (r : Nat) (sc : ℂ) (c : SS.BitString n → ZQ)
    (h : ∀ s, c s ≠ ZQ.zero → exponent a s % q = r) :
    physicalGate zeta a (stC sc c) = fun s => zeta ^ r * stC sc c s := by
  funext s
  by_cases hc : c s = ZQ.zero
  · simp [physicalGate, stC, hc]
  have hp : zeta ^ exponent a s = zeta ^ (exponent a s % q) := by
    calc
      zeta ^ exponent a s = zeta ^ (exponent a s % q + q * (exponent a s / q)) := by rw [Nat.mod_add_div]
      _ = _ := by rw [pow_add, pow_mul, hz, one_pow, mul_one]
  simp only [physicalGate, Finset.prod_pow_eq_pow_sum]
  change zeta ^ exponent a s * _ = _
  rw [hp, h s hc]

def encode (sc : ℂ) (c : Fin K → SS.BitString n → ZQ) (alpha : Fin K → ℂ) : SS.State n ℂ :=
  fun s => ∑ j, alpha j * stC sc (c j) s

theorem physical_logical (zeta : ℂ) (q : Nat) (hz : zeta ^ q = 1)
    (a : Fin n → Nat) (r : Fin K → Nat) (sc : ℂ) (c : Fin K → SS.BitString n → ZQ)
    (h : ∀ j s, c j s ≠ ZQ.zero → exponent a s % q = r j) (alpha : Fin K → ℂ) :
    physicalGate zeta a (encode sc c alpha) = encode sc c (fun j => zeta ^ r j * alpha j) := by
  funext s
  simp only [physicalGate, encode, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he := congrFun (physical_word zeta q hz a (r j) sc (c j) (h j)) s
  simp only [physicalGate] at he
  calc
    _ = alpha j * ((∏ i, zeta ^ (if s i then a i else 0)) * stC sc (c j) s) := by ring
    _ = _ := by rw [he]; ring

end
end SS.ExactCode


