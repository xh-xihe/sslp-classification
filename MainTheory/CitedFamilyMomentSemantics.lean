import MainTheory.CitedFamilyMomentData
import MainTheory.CitedCorrectedFamily

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.CitedFamilyMomentSemantics

open SixQubit.Realize MainTheory.CitedFamilyMomentData MainTheory.FiveQubitPerfectCore
open MainTheory.FiveQubitCitedGateSemantics

noncomputable def word (i : Fin 2) (b : Bool) : SS.State 6 ℂ := stC scale (base i b)

theorem base_semantics (i : Fin 2) (b : Bool) (x : SS.BitString 6) :
    word i b x=if x 5=b then
      MainTheory.CitedCorrectedFamily.sign (x 4) b*constructed i (Fin.init x) else 0 := by
  have h := constructed_coordinate i ⟨number (Fin.init x),number_lt _⟩
  simp only [bits_number] at h
  unfold word stC base
  split_ifs with hx hb
  · rw [h]
    simp only [MainTheory.FiveQubitCitedGateResidual.word,toC_neg,
      MainTheory.CitedCorrectedFamily.sign,hb,if_true]
    ring
  · rw [h]
    simp [MainTheory.FiveQubitCitedGateResidual.word,
      MainTheory.CitedCorrectedFamily.sign,hb]
  · simp

theorem mass_scale : star scale*scale*toC mass=1 := by
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hb : MainTheory.CitedSingleQubitMatrices.coefficientB^2=(3+Real.sqrt 3)/6 :=
    Real.sq_sqrt (by positivity)
  have he : (MainTheory.CitedSingleQubitMatrices.coefficientB/8)^2*(192-64*Real.sqrt 3)=1 := by
    rw [div_pow,hb]
    norm_num
    nlinarith
  apply Complex.ext
  · simpa [scale,mass,toC,toCre,toCim,rz,SS.rp,z8,pow_two] using he
  · simp [scale,mass,toC,toCre,toCim,rz,SS.rp,z8]

theorem expansion (theta : ℝ) (i : Fin 2) :
    MainTheory.CitedAncillaFamily.code theta i=
      (Real.cos (theta/2) : ℂ) • word i false+(Real.sin (theta/2) : ℂ) • word i true := by
  funext x
  obtain ⟨⟨b,x⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin 6 => Bool)).surjective x
  change MainTheory.CitedAncillaFamily.code theta i (Fin.snoc x b)=_
  rw [MainTheory.CitedCorrectedFamily.code_snoc]
  change _ = (Real.cos (theta/2) : ℂ)*word i false (Fin.snoc x b)+
    (Real.sin (theta/2) : ℂ)*word i true (Fin.snoc x b)
  rw [base_semantics,base_semantics]
  have h4 : (Fin.snoc x b : SS.BitString 6) (4 : Fin 6)=x 4 :=
    Fin.snoc_castSucc (α := fun _ : Fin 6 => Bool) b x 4
  have h5 : (Fin.snoc x b : SS.BitString 6) (5 : Fin 6)=b :=
    Fin.snoc_last (α := fun _ : Fin 6 => Bool) b x
  rw [h4,h5,Fin.init_snoc]
  cases b <;> simp [MainTheory.CitedCorrectedFamily.amplitude,mul_assoc]

end MainTheory.CitedFamilyMomentSemantics
