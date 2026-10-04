import MainTheory.HomogeneousCompletionNormalization
import MainTheory.OrderTwoScalarBridge
import MainTheory.Orbit2FullImage
import MainTheory.Orbit3FullImage

/-! Raw positive-norm parity encoders satisfy the literal normalized conclusions. -/

namespace MainTheory.OrderTwoHomogeneousEncoders
noncomputable section
open MainTheory.CubeAction MainTheory.CubeCompletionTransport
open MainTheory.OrderTwoScalarBridge MainTheory.HomogeneousCompletionNormalization
open MainTheory.DirectoryEnumeratorImages
open SixQubit.ParityPauliScalars
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem orbit2_fiber_iff : ∀ k : Fin 2, ∀ x : SS.BitString 6,
    x ∈ angleFibers SixQubit.OpenLOrbit2.angle (finColor k) ↔
      SS.bdot orbit2Mask x=(k==1) := by decide +kernel

theorem orbit3_fiber_iff : ∀ k : Fin 2, ∀ x : SS.BitString 6,
    x ∈ angleFibers SixQubit.OpenLOrbit3.angle (finColor k) ↔
      SS.bdot orbit3Mask x=(k==1) := by decide +kernel

theorem support_of_parity {mask : SS.BitString 6} {F : FiberPair 6}
    (hF : ∀ k : Fin 2, ∀ x : SS.BitString 6,
      x ∈ F (finColor k) ↔ SS.bdot mask x=(k==1))
    (ψ : Fin 2 → SS.State 6 ℂ) (hψ : ParityPair mask ψ) :
    ∀ k x, x ∉ F (finColor k) → ψ k x=0 := by
  intro k x hx
  apply hψ k x
  intro he
  apply hx
  rw [hF]
  have hb := chi_bdot mask x
  rw [he] at hb
  have hk : (if k==1 then (-1 : ℝ) else 1)=logicalSign k := by
    fin_cases k <;> norm_num [logicalSign]
  have hbit (a b : Bool) :
      (if a then (-1 : ℝ) else 1)=(if b then (-1 : ℝ) else 1) → a=b := by
    cases a <;> cases b <;> norm_num
  exact hbit _ _ (hb.symm.trans hk.symm)

def orbit2 (ψ : Fin 2 → SS.State 6 ℂ) (N : ℝ) (hN : 0 < N)
    (hn : ∀ k, SS.innerC (ψ k) (ψ k)=(N : ℂ))
    (hp : ParityPair orbit2Mask ψ) (hKL : SS.HasDistance ψ 3) :
    Raw (angleFibers SixQubit.OpenLOrbit2.angle) where
  states := ψ
  norm := N
  positive := hN
  norms := hn
  supported := support_of_parity orbit2_fiber_iff ψ hp
  hasDistance := hKL

def orbit3 (ψ : Fin 2 → SS.State 6 ℂ) (N : ℝ) (hN : 0 < N)
    (hn : ∀ k, SS.innerC (ψ k) (ψ k)=(N : ℂ))
    (hp : ParityPair orbit3Mask ψ) (hKL : SS.HasDistance ψ 3) :
    Raw (angleFibers SixQubit.OpenLOrbit3.angle) where
  states := ψ
  norm := N
  positive := hN
  norms := hn
  supported := support_of_parity orbit3_fiber_iff ψ hp
  hasDistance := hKL

theorem orbit2_A3_zero (R : Raw (angleFibers SixQubit.OpenLOrbit2.angle)) :
    SS.MacWilliams.Aco R.states 3=0 := by
  have h := MainTheory.Orbit2FullImage.actual_A3_zero (completion R)
  rw [enumerator, div_eq_zero_iff] at h
  exact h.resolve_right (pow_ne_zero _ (ne_of_gt R.positive))

theorem orbit3_A3_zero (R : Raw (angleFibers SixQubit.OpenLOrbit3.angle)) :
    SS.MacWilliams.Aco R.states 3=0 := by
  have h := MainTheory.Orbit3FullImage.actual_A3_zero (completion R)
  rw [enumerator, div_eq_zero_iff] at h
  exact h.resolve_right (pow_ne_zero _ (ne_of_gt R.positive))

theorem orbit3_enumerator (R : Raw (angleFibers SixQubit.OpenLOrbit3.angle)) :
    0 ≤ SS.MacWilliams.Aco R.states 1/(4*R.norm^2) ∧
    SS.MacWilliams.Aco R.states 1/(4*R.norm^2) ≤ 1 ∧
    (fun w : Fin 7 => SS.MacWilliams.Aco R.states w/(4*R.norm^2))=
      MainTheory.WImages.FI (SS.MacWilliams.Aco R.states 1/(4*R.norm^2)) := by
  simpa only [enumerator, div_div, mul_comm (R.norm^2)] using
    MainTheory.Orbit3FullImage.actual_enumerator (completion R)

theorem orbit2_enumerator (R : Raw (angleFibers SixQubit.OpenLOrbit2.angle)) :
    0 ≤ SS.MacWilliams.Aco R.states 1/(4*R.norm^2) ∧
    SS.MacWilliams.Aco R.states 1/(4*R.norm^2) ≤ 1 ∧
    (fun w : Fin 7 => SS.MacWilliams.Aco R.states w/(4*R.norm^2))=
      MainTheory.WImages.FI (SS.MacWilliams.Aco R.states 1/(4*R.norm^2)) := by
  simpa only [enumerator, div_div, mul_comm (R.norm^2)] using
    MainTheory.Orbit2FullImage.actual_enumerator (completion R)

end
end MainTheory.OrderTwoHomogeneousEncoders
