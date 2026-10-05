import SixQubit.CodeOrbit34
import SixQubit.CodeOrbit39

/-! Every index in the printed orbit-34 two-row system, and the literal
five-source/five-character orbit-39 matrix. Ordinary kernel reduction only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderFiveWalshRemainingDisplays
open scoped BigOperators Matrix
noncomputable section

namespace Orbit34
open SixQubit.Orbit34
def zero : SS.BitString 6 := fun _ => false
def ones : SS.BitString 6 := fun _ => true
def point (i : Fin 6) : SS.BitString 6 := SS.stdBasis i

theorem incidence_all : ∀ i,
    S1.filter (fun y => SS.bxor y (point i) ∈ S0)={point i,ones} := by decide +kernel
theorem pair_ne : ∀ i, point i≠ones := by decide +kernel
theorem flip_images : ∀ i, SS.bxor (point i) (point i)=zero ∧
    SS.bxor ones (point i)=SS.complement (point i) := by decide +kernel
theorem zero_signs : ∀ i, SS.bdot zero (point i)=false ∧ SS.bdot zero ones=false := by decide +kernel
theorem separating_signs : ∀ i j, i≠j →
    SS.bdot (point j) (point i)=false ∧ SS.bdot (point j) ones=true := by decide +kernel
theorem weights : ∀ i j, (⟨point i,zero⟩ : SS.PauliString 6).wt≤2 ∧
    (⟨point i,point j⟩ : SS.PauliString 6).wt≤2 := by decide +kernel

theorem expand_X (c d : SS.State 6 ℂ) (i : Fin 6) :
    offSum c d (point i) zero=star (c zero)*d (point i)+star (c (SS.complement (point i)))*d ones := by
  unfold offSum
  rw [incidence_all,Finset.sum_pair (pair_ne i),(flip_images i).1,(flip_images i).2]
  simp only [(zero_signs i).1,(zero_signs i).2,SixQubit.signMul_false]

theorem expand_XZ (c d : SS.State 6 ℂ) (i j : Fin 6) (hij : i≠j) :
    offSum c d (point i) (point j)=star (c zero)*d (point i)-star (c (SS.complement (point i)))*d ones := by
  unfold offSum
  rw [incidence_all,Finset.sum_pair (pair_ne i),(flip_images i).1,(flip_images i).2]
  simp only [(separating_signs i j hij).1,(separating_signs i j hij).2,
    SixQubit.signMul_false,SixQubit.signMul_true,sub_eq_add_neg]

theorem physical_two_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i j : Fin 6) (hij : i≠j) :
    star (c zero)*d (point i)+star (c (SS.complement (point i)))*d ones=0 ∧
    star (c zero)*d (point i)-star (c (SS.complement (point i)))*d ones=0 := by
  have hx : offSum c d (point i) zero=0 :=
    SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl _ _ (weights i j).1
  have hz : offSum c d (point i) (point j)=0 :=
    SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl _ _ (weights i j).2
  rw [expand_X] at hx
  rw [expand_XZ c d i j hij] at hz
  exact ⟨hx,hz⟩
end Orbit34

namespace Orbit39
open SixQubit.Orbit39
def sources : Fin 5 → SS.BitString 6 := ![y0,y1,y2,y3,y4]
def destinations : Fin 5 → SS.BitString 6 := ![z8,z9,z10,z11,z12]
def characters : Fin 5 → SS.BitString 6 :=
  ![w0,SS.stdBasis 1,SS.stdBasis 2,SS.stdBasis 3,SS.stdBasis 4]
def W : Matrix (Fin 5) (Fin 5) ℚ :=
  fun i j => if SS.bdot (characters i) (destinations j) then -1 else 1
theorem actual_images : ∀ j, SS.bxor (destinations j) ef=sources j := by decide +kernel
theorem actual_incidence : S1.filter (fun y => SS.bxor y ef ∈ S0)=
    Finset.univ.image destinations := by decide +kernel
theorem source_characters : W=fun i j => if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem determinant : Matrix.det W=16 := by decide +kernel
end Orbit39

end
end MainTheory.OrderFiveWalshRemainingDisplays
