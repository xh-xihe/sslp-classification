import MainTheory.QuaternionCliffordAxes

/-! A whole bounded-order subgroup with two perpendicular quarter-turn axes. -/

namespace MainTheory.QuaternionQuarterPair

noncomputable section

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionOrthogonalFrame
  MainTheory.QuaternionAxisGeometry MainTheory.QuaternionCliffordAxes
  MainTheory.QuaternionProjectiveOrders

def Bounded (G : Subgroup (unitary ℍ[ℝ])) : Prop :=
  ∀ g ∈ G, AllowedScalar g.val.re

theorem conjugate_mem (G : Subgroup (unitary ℍ[ℝ])) (g q : unitary ℍ[ℝ])
    (hg : g∈G) (hq : q∈G) : conjugate g q ∈ G :=
  G.mul_mem (G.mul_mem hg hq) (G.inv_mem hg)

theorem related_quarters (G : Subgroup (unitary ℍ[ℝ])) (hG : Bounded G)
    (p q : unitary ℍ[ℝ]) (hp : p∈G) (hq : q∈G)
    (he : p.val.re=q.val.re) (hquarter : 2*q.val.re^2=1) : Related (p^2) (q^2) :=
  quarter_related p q he hquarter (hG _ (G.mul_mem hp hq))
    (hG _ (G.mul_mem hp (G.inv_mem hq)))

theorem common_frame (G : Subgroup (unitary ℍ[ℝ])) (hG : Bounded G)
    (p q : unitary ℍ[ℝ]) (hp : p∈G) (hq : q∈G)
    (he : p.val.re=q.val.re) (hquarter : 2*q.val.re^2=1)
    (ha : Anti (p^2) (q^2)) :
    ∃ u : unitary ℍ[ℝ],∀ g∈G,Normalizes (conjugate u g) := by
  have hpquarter : 2*p.val.re^2=1 := by rw [he]; exact hquarter
  obtain ⟨u,huI,huJ⟩ := ordered_frame (p^2) (q^2)
    (quarter_square_pure p hpquarter) (quarter_square_pure q hquarter) ha
  refine ⟨u,?_⟩
  intro g hg
  have hpi : conjugate u ((conjugate g p)^2)=conjugate (conjugate u g) axisI := by
    rw [← conjugate_pow,conjugate_intertwine,huI]
  have hqj : conjugate u ((conjugate g q)^2)=conjugate (conjugate u g) axisJ := by
    rw [← conjugate_pow,conjugate_intertwine,huJ]
  have hii := conjugate_related u _ _ (related_quarters G hG (conjugate g p) p
    (conjugate_mem G g p hg hp) hp (conjugate_re g p) hpquarter)
  have hij := conjugate_related u _ _ (related_quarters G hG (conjugate g p) q
    (conjugate_mem G g p hg hp) hq ((conjugate_re g p).trans he) hquarter)
  have hji := conjugate_related u _ _ (related_quarters G hG (conjugate g q) p
    (conjugate_mem G g q hg hq) hp ((conjugate_re g q).trans he.symm) hpquarter)
  have hjj := conjugate_related u _ _ (related_quarters G hG (conjugate g q) q
    (conjugate_mem G g q hg hq) hq (conjugate_re g q) hquarter)
  rw [hpi,huI] at hii
  rw [hpi,huJ] at hij
  rw [hqj,huI] at hji
  rw [hqj,huJ] at hjj
  exact normalizes_of_two _
    (coordinate_axis _ (conjugate_pure _ _ axisI_pure) hii hij)
    (coordinate_axis _ (conjugate_pure _ _ axisJ_pure) hji hjj)

theorem nonparallel_orbit (G : Subgroup (unitary ℍ[ℝ])) (hG : Bounded G)
    (q : unitary ℍ[ℝ]) (hq : q∈G) (hquarter : 2*q.val.re^2=1)
    (v : unitary ℍ[ℝ]) (hv : v∈G)
    (hplus : (conjugate v q)^2≠q^2) (hminus : (conjugate v q)^2≠ -(q^2)) :
    ∃ u : unitary ℍ[ℝ],∀ g∈G,Normalizes (conjugate u g) := by
  have hr := related_quarters G hG (conjugate v q) q
    (conjugate_mem G v q hv hq) hq (conjugate_re v q) hquarter
  have ha := (hr.resolve_left hplus).resolve_left hminus
  exact common_frame G hG (conjugate v q) q
    (conjugate_mem G v q hv hq) hq (conjugate_re v q) hquarter ha

end

end MainTheory.QuaternionQuarterPair
