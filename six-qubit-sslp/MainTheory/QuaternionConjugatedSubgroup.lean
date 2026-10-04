import MainTheory.QuaternionQuarterPair

/-! Transport a whole subgroup through one unitary change of basis. -/

namespace MainTheory.QuaternionConjugatedSubgroup

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionOrthogonalFrame
  MainTheory.QuaternionAxisGeometry MainTheory.QuaternionQuarterPair

def conjugation (u : unitary ℍ[ℝ]) : unitary ℍ[ℝ] →* unitary ℍ[ℝ] where
  toFun := conjugate u
  map_one' := by simp [conjugate]
  map_mul' := conjugate_mul u

def rotated (G : Subgroup (unitary ℍ[ℝ])) (u : unitary ℍ[ℝ]) :
    Subgroup (unitary ℍ[ℝ]) := G.map (conjugation u)

theorem rotated_mem (G : Subgroup (unitary ℍ[ℝ])) (u g : unitary ℍ[ℝ]) (hg : g∈G) :
    conjugate u g∈rotated G u := ⟨g,hg,rfl⟩

theorem rotated_bounded (G : Subgroup (unitary ℍ[ℝ])) (u : unitary ℍ[ℝ]) (h : Bounded G) :
    Bounded (rotated G u) := by
  rintro g ⟨v,hv,rfl⟩
  change MainTheory.QuaternionProjectiveOrders.AllowedScalar (conjugate u v).val.re
  rw [conjugate_re]
  exact h v hv

theorem conjugate_inv (u q : unitary ℍ[ℝ]) : conjugate u q⁻¹=(conjugate u q)⁻¹ := by
  simp only [conjugate,mul_inv_rev,inv_inv]
  group

end

end MainTheory.QuaternionConjugatedSubgroup
