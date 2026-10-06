import MainTheory.Orbit7FamilyProjectors

set_option autoImplicit false

namespace MainTheory.Orbit7NormalizedFamily

open SixQubit.Orbit7Universal MainTheory.Orbit7SpinorCoordinates
open MainTheory.Orbit7NormalizedProjectors MainTheory.Orbit7FourHafnians
open MainTheory.Orbit7FamilyProjectors

theorem normalized_family {E : Type*} [DecidableEq E] (F : Finset E)
    (x : E → ℂ) (c d : ℝ) (t p : ℂ) (w : ℝ)
    (hcd : c^2+d^2=1) (hp : Complex.normSq p=Complex.normSq t) (hw : w ≠ 0)
    (hmass : (∑ e ∈ F,∑ i : Fin 2,Complex.normSq (avec c d (x e) (t*x e) i))=w)
    (hf : (fun i j => ∑ e ∈ F,outer (avec c d (x e) (t*x e)) i j) +
      (fun i j => ∑ e ∈ F,outer (bvec (x e) (p*x e)) i j) =
      (w : ℂ) • (outer (![1,0])+outer (nvec c d))) :
    Pa c d t+Pb p=outer (![1,0])+outer (nvec c d) := by
  have ha (e : E) : avec c d (x e) (t*x e) = fun i => x e*avec c d 1 t i := by
    funext i
    fin_cases i <;> simp [avec] <;> ring
  have hb (e : E) : bvec (x e) (p*x e) = fun i => star (x e)*bvec 1 p i := by
    funext i
    fin_cases i <;> simp [bvec]
    ring
  simp_rw [ha] at hmass
  rw [weight_factor F x (avec c d 1 t) _ (Pa_mass c d hcd t)] at hmass
  simp_rw [ha,hb] at hf
  have h := paired_projectors F x (avec c d 1 t) (bvec 1 p)
    (1+Complex.normSq t) w (denominator_positive t) hw hmass _ hf
  simpa only [Pa,Pb,hp] using h

end MainTheory.Orbit7NormalizedFamily
