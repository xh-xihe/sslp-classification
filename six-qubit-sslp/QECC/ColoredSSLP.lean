import QECC.IntrinsicSSLP
import QECC.ColorArithmetic

namespace QECC

open scoped BigOperators

noncomputable section

namespace CodeProjector

variable {n K : ℕ} (C : CodeProjector n K)

/-- Apply the SSLP color embedding pointwise to a family of logical colors. -/
def colorVectorEmbed {ι : Type*} (m q : ℕ) (hmq : m ∣ q) :
    (ι → ZMod m) →+ (ι → ZMod q) where
  toFun gamma := fun i => colorEmbed m q hmq (gamma i)
  map_zero' := by
    funext i
    simp
  map_add' gamma delta := by
    funext i
    simp

theorem colorVectorEmbed_injective {ι : Type*} (m q : ℕ)
    (hm : 2 ≤ m) (hq : 0 < q) (hmq : m ∣ q) :
    Function.Injective (colorVectorEmbed (ι := ι) m q hmq) := by
  intro gamma delta h
  funext i
  apply colorEmbed_injective m q hm hq hmq
  exact congrFun h i

/-- Recover the distinct logical colors from the relative active residues.
The resulting color vector starts at zero and is primitive; equivalently, its
canonical gcd with `m` is one. -/
theorem exists_primitive_sslp_colors
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (H : C.IntrinsicSSLPData U R hpres b0) :
    letI : NeZero R.q :=
      ⟨(lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two).ne'⟩
    ∃ gamma : C.ActiveResidue R.a → ZMod (addOrderOf U),
      gamma b0 = 0 ∧
      Function.Injective gamma ∧
      (∀ b, colorEmbed (addOrderOf U) R.q H.logicalOrder_dvd_physical
          (gamma b) = C.relativeResidues R.a b0 b) ∧
      ColorPrimitive (addOrderOf U) gamma ∧
      colorGCD (addOrderOf U) gamma = 1 := by
  let m := addOrderOf U
  have hm : 2 ≤ m := H.logicalOrder_gt_one
  have hmpos : 0 < m := by omega
  have hq : 0 < R.q := lt_of_lt_of_le Nat.zero_lt_two R.q_ge_two
  letI : NeZero R.q := ⟨hq.ne'⟩
  have hkill : m • C.relativeResidues R.a b0 = 0 := by
    change (addOrderOf U) • C.relativeResidues R.a b0 = 0
    rw [← H.relativeOrder]
    exact addOrderOf_nsmul_eq_zero _
  have hkillAt (b : C.ActiveResidue R.a) :
      m • C.relativeResidues R.a b0 b = 0 := by
    exact congrFun hkill b
  have hcolors (b : C.ActiveResidue R.a) :
      ∃! gamma : ZMod m,
        colorEmbed m R.q H.logicalOrder_dvd_physical gamma =
          C.relativeResidues R.a b0 b :=
    existsUnique_color_of_nsmul_eq_zero m R.q hm hq
      H.logicalOrder_dvd_physical _ (hkillAt b)
  choose gamma hgamma _ using hcolors
  have hgamma0 : gamma b0 = 0 := by
    apply colorEmbed_injective m R.q hm hq H.logicalOrder_dvd_physical
    rw [hgamma]
    simp [relativeResidues]
  have hgammaInj : Function.Injective gamma := by
    intro b c hbc
    apply H.relativeInjective
    rw [← hgamma b, ← hgamma c, hbc]
  have horderEmbed :
      addOrderOf
          (colorVectorEmbed m R.q H.logicalOrder_dvd_physical gamma) =
        addOrderOf gamma :=
    addOrderOf_injective
      (colorVectorEmbed m R.q H.logicalOrder_dvd_physical)
      (colorVectorEmbed_injective m R.q hm hq
        H.logicalOrder_dvd_physical) gamma
  have hembed :
      colorVectorEmbed m R.q H.logicalOrder_dvd_physical gamma =
        C.relativeResidues R.a b0 := by
    funext b
    exact hgamma b
  have hprimitive : ColorPrimitive m gamma := by
    change addOrderOf gamma = m
    rw [← horderEmbed, hembed, H.relativeOrder]
  have hgcd : colorGCD m gamma = 1 :=
    (colorPrimitive_iff_gcd_eq_one m hmpos gamma).1 hprimitive
  exact ⟨gamma, hgamma0, hgammaInj, hgamma, hprimitive, hgcd⟩

/-- A pointwise statement of the paper's formula
`b = (q / m) * gamma`: every normalized active residue has that unique form
using canonical representatives. -/
theorem sslp_color_residue_formula
    (U : C.ProjectiveDiagonalGroup)
    (R : ReducedDiagonalRepresentative n)
    (hpres : C.Preserves R.phase)
    (b0 : C.ActiveResidue R.a)
    (H : C.IntrinsicSSLPData U R hpres b0) :
    ∃ gamma : C.ActiveResidue R.a → ZMod (addOrderOf U),
      ∀ b,
        C.relativeResidues R.a b0 b =
          (((R.q / addOrderOf U : ℕ) : ZMod R.q) *
            ((gamma b).val : ZMod R.q)) := by
  obtain ⟨gamma, _, _, hgamma, _, _⟩ :=
    C.exists_primitive_sslp_colors U R hpres b0 H
  refine ⟨gamma, fun b => ?_⟩
  rw [← hgamma b]
  exact colorEmbed_apply (addOrderOf U) R.q
    (lt_trans Nat.zero_lt_one H.logicalOrder_gt_one)
    H.logicalOrder_dvd_physical (gamma b)

end CodeProjector

end

end QECC
