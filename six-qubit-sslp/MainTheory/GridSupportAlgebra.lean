import Mathlib

/-! The support and permanent argument for two grid rows, retaining zeros.
Each intermediate implication is independent of the final odd-cycle no-go.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.GridSupportAlgebra
open scoped BigOperators
noncomputable section

def rowSupport (b : Fin 2 → Fin 4 → ℂ) (i : Fin 2) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => b i j≠0)

theorem nonempty_of_mass (b : Fin 4 → ℂ) (h : 0<∑ j, Complex.normSq (b j)) :
    ∃ j, b j≠0 := by
  by_contra hh
  push_neg at hh
  simp only [hh,Complex.normSq_zero,Finset.sum_const_zero] at h
  exact (lt_irrefl 0) h

theorem full_support (b : Fin 2 → Fin 4 → ℂ)
    (hrow : ∀ i, ∃ j, b i j≠0) (hcol : ∀ j, b 0 j≠0 ∨ b 1 j≠0)
    (hperm : ∀ j k, j≠k → b 0 j*b 1 k+b 0 k*b 1 j=0) :
    ∀ j, b 0 j≠0 ∧ b 1 j≠0 := by
  intro j
  constructor
  · intro hz
    have hj := (hcol j).resolve_left (by simp [hz])
    obtain ⟨k,hk⟩ := hrow 0
    have hne : j≠k := by intro he; rw [← he,hz] at hk; exact hk rfl
    have hp := hperm j k hne
    rw [hz,zero_mul,zero_add] at hp
    exact (mul_ne_zero hk hj) hp
  · intro hz
    have hj := (hcol j).resolve_right (by simp [hz])
    obtain ⟨k,hk⟩ := hrow 1
    have hne : j≠k := by intro he; rw [← he,hz] at hk; exact hk rfl
    have hp := hperm j k hne
    rw [hz,mul_zero,add_zero] at hp
    exact (mul_ne_zero hj hk) hp

theorem supports_univ (b : Fin 2 → Fin 4 → ℂ)
    (hrow : ∀ i, ∃ j, b i j≠0) (hcol : ∀ j, b 0 j≠0 ∨ b 1 j≠0)
    (hperm : ∀ j k, j≠k → b 0 j*b 1 k+b 0 k*b 1 j=0) :
    rowSupport b 0=Finset.univ ∧ rowSupport b 1=Finset.univ := by
  have hf := full_support b hrow hcol hperm
  constructor
  · ext j; simp [rowSupport,(hf j).1]
  · ext j; simp [rowSupport,(hf j).2]

theorem permanent_from_weighted_phase
    (x0 x1 y0 y1 dx0 dx1 dy0 dy1 k : ℂ) (hk : k≠0)
    (hx0 : star dx0=k*x0) (hx1 : star dx1=k*x1)
    (hy0 : star dy0=k*y0) (hy1 : star dy1=k*y1)
    (h : star x0*dy1+star x1*dy0+star y0*dx1+star y1*dx0=0) :
    x0*y1+x1*y0=0 := by
  have he := congrArg star h
  simp only [star_add,star_mul',star_star,star_zero] at he
  have hp : k*(x0*y1+x1*y0)=0 := by
    linear_combination (1/2 : ℂ)*he-(x0/2)*hy1-(x1/2)*hy0-(y0/2)*hx1-(y1/2)*hx0
  exact (mul_eq_zero.mp hp).resolve_left hk

end
end MainTheory.GridSupportAlgebra
