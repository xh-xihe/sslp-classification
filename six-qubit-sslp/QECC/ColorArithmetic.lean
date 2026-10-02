import QECC.FirstTheorem

namespace QECC

noncomputable section

/-- Embed a logical color modulo `m` into residues modulo `q` by multiplying
an integer representative by `q / m`. -/
def colorEmbed (m q : ℕ) (hmq : m ∣ q) : ZMod m →+ ZMod q := by
  let f : ℤ →+ ZMod q :=
    (AddMonoidHom.mulLeft (q / m : ZMod q)).comp (Int.castAddHom (ZMod q))
  have hf : f m = 0 := by
    dsimp [f]
    norm_num
    rw [← Nat.cast_mul, Nat.div_mul_cancel hmq, ZMod.natCast_self]
  exact (ZMod.lift m) ⟨f, hf⟩

/-- Formula for `colorEmbed` on an arbitrary integer representative. -/
@[simp] theorem colorEmbed_intCast (m q : ℕ) (hmq : m ∣ q) (z : ℤ) :
    colorEmbed m q hmq (z : ZMod m) =
      ((q / m : ℕ) : ZMod q) * (z : ZMod q) := by
  simp [colorEmbed]

/-- Formula for `colorEmbed` using the canonical representative of a color. -/
theorem colorEmbed_apply (m q : ℕ) (hm : 0 < m) (hmq : m ∣ q)
    (gamma : ZMod m) :
    colorEmbed m q hmq gamma =
      ((q / m : ℕ) : ZMod q) * (gamma.val : ZMod q) := by
  letI : NeZero m := ⟨hm.ne'⟩
  calc
    colorEmbed m q hmq gamma = colorEmbed m q hmq (gamma.val : ZMod m) := by
      rw [ZMod.natCast_zmod_val]
    _ = ((q / m : ℕ) : ZMod q) * (gamma.val : ZMod q) := by
      simpa using colorEmbed_intCast m q hmq (gamma.val : ℤ)

/-- Multiplication by `q / m` injects `ZMod m` into `ZMod q` when both
moduli are positive and `m` divides `q`. -/
theorem colorEmbed_injective (m q : ℕ) (hm : 2 ≤ m) (hq : 0 < q)
    (hmq : m ∣ q) :
    Function.Injective (colorEmbed m q hmq) := by
  rw [← AddMonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
    rw [colorEmbed_intCast] at hx
    have hx' : ((((q / m : ℕ) : ℤ) * z : ℤ) : ZMod q) = 0 := by
      rw [Int.cast_mul, Int.cast_natCast]
      exact hx
    have hdiv : (q : ℤ) ∣ ((q / m : ℕ) : ℤ) * z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx'
    have hkpos : 0 < q / m :=
      Nat.div_pos (Nat.le_of_dvd hq hmq) (by omega)
    have hqfac : (q : ℤ) = ((q / m : ℕ) : ℤ) * (m : ℤ) := by
      exact_mod_cast (Nat.div_mul_cancel hmq).symm
    rw [hqfac] at hdiv
    have hmdvd : (m : ℤ) ∣ z :=
      Int.dvd_of_mul_dvd_mul_left (by exact_mod_cast hkpos.ne') hdiv
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd z m).2 hmdvd
  · exact bot_le

/-- The subgroup of residues modulo `q` killed by multiplication by `m`. -/
def colorTorsion (m q : ℕ) : AddSubgroup (ZMod q) where
  carrier := {b | m • b = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change m • x = 0 at hx
    change m • y = 0 at hy
    change m • (x + y) = 0
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' := by
    intro x hx
    change m • x = 0 at hx
    change m • (-x) = 0
    rw [neg_nsmul, hx, neg_zero]

@[simp] theorem mem_colorTorsion {m q : ℕ} (b : ZMod q) :
    b ∈ colorTorsion m q ↔ m • b = 0 :=
  Iff.rfl

/-- The image of the color embedding consists exactly of the `m`-torsion
residues modulo `q`. -/
theorem mem_range_colorEmbed_iff (m q : ℕ) (hm : 2 ≤ m) (hmq : m ∣ q)
    (b : ZMod q) :
    b ∈ Set.range (colorEmbed m q hmq) ↔ m • b = 0 := by
  constructor
  · rintro ⟨gamma, rfl⟩
    rw [← map_nsmul]
    have hmzero : m • gamma = 0 := by
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hmzero, map_zero]
  · intro hb
    obtain ⟨z, rfl⟩ := ZMod.intCast_surjective b
    have hb' : ((((m : ℕ) : ℤ) * z : ℤ) : ZMod q) = 0 := by
      rw [Int.cast_mul, Int.cast_natCast]
      simpa [nsmul_eq_mul] using hb
    have hdiv : (q : ℤ) ∣ (m : ℤ) * z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb'
    have hqfac : (q : ℤ) = (m : ℤ) * ((q / m : ℕ) : ℤ) := by
      exact_mod_cast (Nat.mul_div_cancel' hmq).symm
    rw [hqfac] at hdiv
    have hkdiv : (((q / m : ℕ) : ℤ)) ∣ z :=
      Int.dvd_of_mul_dvd_mul_left (by omega) hdiv
    obtain ⟨w, rfl⟩ := hkdiv
    refine ⟨(w : ZMod m), ?_⟩
    rw [colorEmbed_intCast, Int.cast_mul, Int.cast_natCast]

/-- Every `m`-torsion residue modulo `q` has a unique logical color. -/
theorem existsUnique_color_of_nsmul_eq_zero (m q : ℕ) (hm : 2 ≤ m)
    (hq : 0 < q) (hmq : m ∣ q) (b : ZMod q) (hb : m • b = 0) :
    ∃! gamma : ZMod m, colorEmbed m q hmq gamma = b := by
  obtain ⟨gamma, hgamma⟩ :=
    (mem_range_colorEmbed_iff m q hm hmq b).2 hb
  refine ⟨gamma, hgamma, ?_⟩
  intro delta hdelta
  apply colorEmbed_injective m q hm hq hmq
  exact hdelta.trans hgamma.symm

/-- The color embedding identifies `ZMod m` with the `m`-torsion subgroup
of `ZMod q`. -/
noncomputable def colorTorsionEquiv (m q : ℕ) (hm : 2 ≤ m) (hq : 0 < q)
    (hmq : m ∣ q) :
    ZMod m ≃+ colorTorsion m q := by
  let f : ZMod m →+ colorTorsion m q :=
    (colorEmbed m q hmq).codRestrict (colorTorsion m q) fun gamma ↦
      (mem_range_colorEmbed_iff m q hm hmq (colorEmbed m q hmq gamma)).1
        ⟨gamma, rfl⟩
  apply AddEquiv.ofBijective f
  constructor
  · intro x y hxy
    apply colorEmbed_injective m q hm hq hmq
    exact congr_arg Subtype.val hxy
  · intro b
    obtain ⟨gamma, hgamma⟩ :=
      (mem_range_colorEmbed_iff m q hm hmq b.1).2 b.2
    exact ⟨gamma, Subtype.ext hgamma⟩

private theorem finset_lcm_div_gcd {iota : Type*} (s : Finset iota)
    (f : iota → ℕ) (m : ℕ) (hm : 0 < m) :
    s.lcm (fun i ↦ m / Nat.gcd m (f i)) =
      m / Nat.gcd m (s.gcd f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.lcm_empty, Finset.gcd_empty, Nat.gcd_zero_right]
      rw [Nat.div_self hm]
  | @insert a s ha ih =>
      rw [Finset.lcm_insert, Finset.gcd_insert, ih]
      change Nat.lcm (m / Nat.gcd m (f a))
        (m / Nat.gcd m (s.gcd f)) = _
      rw [Nat.div_lcm_eq_div_gcd
        (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)]
      apply congrArg (fun d ↦ m / d)
      simp [Nat.gcd_left_comm, Nat.gcd_comm]
      rfl

/-- The canonical gcd of a vector of colors, using representatives in
`{0, ..., m - 1}` and including the modulus `m`. -/
def colorGCD {iota : Type*} [Fintype iota]
    (m : ℕ) (gamma : iota → ZMod m) : ℕ :=
  Nat.gcd m (Finset.univ.gcd fun i ↦ (gamma i).val)

/-- A color vector is primitive when its exact additive order is its modulus. -/
def ColorPrimitive {iota : Type*} [Fintype iota]
    (m : ℕ) (gamma : iota → ZMod m) : Prop :=
  addOrderOf gamma = m

/-- Exact additive order of a finite vector of colors. -/
theorem addOrderOf_colorVector {iota : Type*} [Fintype iota]
    (m : ℕ) (hm : 0 < m) (gamma : iota → ZMod m) :
    addOrderOf gamma = m / colorGCD m gamma := by
  letI : NeZero m := ⟨hm.ne'⟩
  rw [Pi.addOrderOf]
  calc
    Finset.univ.lcm (fun i ↦ addOrderOf (gamma i)) =
        Finset.univ.lcm (fun i ↦ m / Nat.gcd m (gamma i).val) := by
      apply Finset.lcm_congr rfl
      intro i _
      calc
        addOrderOf (gamma i) =
            addOrderOf ((gamma i).val : ZMod m) := by
          rw [ZMod.natCast_zmod_val]
        _ = m / Nat.gcd m (gamma i).val :=
          ZMod.addOrderOf_coe _ hm.ne'
    _ = m / colorGCD m gamma := by
      exact finset_lcm_div_gcd Finset.univ (fun i ↦ (gamma i).val) m hm

/-- Primitivity is equivalent to the canonical gcd-one condition from the
SSLP color data. -/
theorem colorPrimitive_iff_gcd_eq_one {iota : Type*} [Fintype iota]
    (m : ℕ) (hm : 0 < m) (gamma : iota → ZMod m) :
    ColorPrimitive m gamma ↔ colorGCD m gamma = 1 := by
  rw [ColorPrimitive, addOrderOf_colorVector m hm gamma, Nat.div_eq_self]
  omega

/-- A unit modulo `m` has a unit lift modulo any positive multiple `q`,
chosen to reduce to its inverse. -/
theorem exists_unit_lift_inverse {m q : ℕ} (hq : 0 < q) (hmq : m ∣ q)
    (gamma : (ZMod m)ˣ) :
    ∃ u : (ZMod q)ˣ, ZMod.unitsMap hmq u = gamma⁻¹ := by
  letI : NeZero q := ⟨hq.ne'⟩
  exact ZMod.unitsMap_surjective hmq gamma⁻¹

/-- Element-level form of `exists_unit_lift_inverse`: the reduction of the
lifted unit normalizes `gamma` to one modulo `m`. -/
theorem exists_unit_lift_mul_eq_one {m q : ℕ} (hq : 0 < q) (hmq : m ∣ q)
    (gamma : ZMod m) (hgamma : IsUnit gamma) :
    ∃ u : (ZMod q)ˣ,
      ((ZMod.unitsMap hmq u : (ZMod m)ˣ) : ZMod m) * gamma = 1 := by
  rcases hgamma with ⟨gammaUnit, rfl⟩
  obtain ⟨u, hu⟩ := exists_unit_lift_inverse hq hmq gammaUnit
  refine ⟨u, ?_⟩
  change (↑(ZMod.unitsMap hmq u) : ZMod m) * (gammaUnit : ZMod m) = 1
  rw [hu]
  simp

end

end QECC
