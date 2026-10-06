import MainTheory.SplitFamilyLogicalCompletion
import MainTheory.PermutationSemanticTransport
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
namespace MainTheory.SplitFamilyTableCertification
open scoped Matrix BigOperators
open MainTheory.SplitFamilyLogicalCompletion MainTheory.PrimitiveSplitDisplays
open Orbit2.TensorPauli MainTheory.PermutationSemanticTransport
noncomputable section

def five (r : Fin 4) : Bool := r.val≥2
def two (r : Fin 4) : Bool := r.val%2=1
def angle (f t : Bool) : Fin 6 → ZMod 2 := fun i => if physicalMask f t i=0 then 0 else 1
def pauli (f t : Bool) : SS.PauliString 6 := ⟨fun _ => false,fun i => physicalMask f t i≠0⟩

theorem pauli_label : ∀ f t,Orbit2.HilbertBridge.label (pauli f t)=physicalMask f t := by decide +kernel
theorem angle_parity : ∀ (f t : Bool) (x : SS.BitString 6),
    (SS.weight (angle f t) x).val=if SS.bdot (pauli f t).z x then 1 else 0 := by decide +kernel
theorem no_Y : ∀ f t,(pauli f t).numY=0 := by decide +kernel

theorem gate_eq_pauli (f t : Bool) (psi : SS.State 6 ℂ) :
    MainTheory.Gate.gate (-1) (angle f t) psi=SS.pauliAct (pauli f t) psi := by
  funext x
  have hx : SS.bxor x (pauli f t).x=x := by
    funext i
    change xor (x i) false=x i
    simp
  simp only [MainTheory.Gate.gate,MainTheory.Gate.diag,angle_parity,SS.pauliAct,
    no_Y,pow_zero,one_mul,hx,SS.signC]
  split_ifs <;> simp

theorem encoder_orthonormal (f t : Bool) (theta : ℝ) (j k : Fin 2) :
    SS.innerC (Orbit2.HilbertBridge.words (encoder f t theta) j)
      (Orbit2.HilbertBridge.words (encoder f t theta) k)=if j=k then 1 else 0 := by
  have he := Orbit2.HilbertBridge.compression (encoder f t theta) (Orbit2.identityPauli 6) j k
  have hz : Orbit2.HilbertBridge.label (Orbit2.identityPauli 6)=(fun _ => 0) := rfl
  rw [Orbit2.pauliAct_identity,hz,operator_zero,Matrix.mul_one,encoder_isometry] at he
  simpa only [Matrix.one_apply] using he

theorem encoder_gate (f t : Bool) (theta : ℝ) (j : Fin 2) :
    MainTheory.Gate.gate (-1) (angle f t) (Orbit2.HilbertBridge.words (encoder f t theta) j)=
      (if j=0 then (1 : ℂ) else -1) • Orbit2.HilbertBridge.words (encoder f t theta) j := by
  rw [gate_eq_pauli]
  funext x
  have ha := Orbit2.HilbertBridge.pauli_action (pauli f t)
    (Orbit2.HilbertBridge.words (encoder f t theta) j) x
  simp only [Orbit2.HilbertBridge.words,Equiv.apply_symm_apply,pauli_label] at ha
  have he := congrArg (fun M => M (Orbit2.HilbertBridge.bitsEquiv 6 x) j) (encoder_logical f t theta)
  dsimp only at he
  simp only [Orbit2.zTwo,Matrix.mul_diagonal] at he
  have hv : (![1,-1] : Fin 2 → ℂ) j=(if j=0 then 1 else -1) := by
    fin_cases j <;> rfl
  rw [hv] at he
  rw [← ha]
  simp only [Pi.smul_apply,smul_eq_mul,Orbit2.HilbertBridge.words]
  simpa only [Matrix.mul_apply,mul_comm] using he

def forward (r : Fin 4) : Fin 6 → Fin 6 :=
  ![![1,4,5,0,2,3],![4,5,0,1,2,3],![1,0,2,3,4,5],![0,1,2,3,4,5]] r
def backward (r : Fin 4) : Fin 6 → Fin 6 :=
  ![![3,0,4,5,1,2],![2,3,4,5,0,1],![1,0,2,3,4,5],![0,1,2,3,4,5]] r
theorem inverse_coordinates : ∀ r i,forward r (backward r i)=i ∧ backward r (forward r i)=i := by decide +kernel
def coordinateEquiv (r : Fin 4) : Equiv.Perm (Fin 6) :=
  ⟨forward r,backward r,fun i => (inverse_coordinates r i).2,fun i => (inverse_coordinates r i).1⟩
def sigma (r : Fin 4) := (coordinateEquiv r).symm
def tableWords (r : Fin 4) (theta : ℝ) (j : Fin 2) : SS.State 6 ℂ :=
  SixQubit.CodeEquiv.permAct (sigma r) (Orbit2.HilbertBridge.words (encoder (five r) (two r) theta) j)

theorem table_angles : ∀ r,permAngle (sigma r) (angle (five r) (two r))=
    (fun i => (records r i : ZMod 2)) := by decide +kernel

theorem table_primitive (r : Fin 4) : MainTheory.Gate.Primitive 2 (fun i => (records r i : ZMod 2)) := by
  have hlast : ((records r 5 : ZMod 2)).val=1 := by
    have h : ∀ s : Fin 4,((records s 5 : ZMod 2)).val=1 := by decide +kernel
    exact h r
  intro d _ hall
  have hd := hall 5
  rw [hlast] at hd
  exact Nat.dvd_one.mp hd

theorem logical_values_distinct : (1 : ℂ)≠-1 := by norm_num

theorem table_distance (r : Fin 4) (theta : ℝ) : SS.HasDistance (tableWords r theta) 3 :=
  hasDistance_permAct (sigma r) _ (encoder_distance (five r) (two r) theta)

theorem table_orthonormal (r : Fin 4) (theta : ℝ) (j k : Fin 2) :
    SS.innerC (tableWords r theta j) (tableWords r theta k)=if j=k then 1 else 0 := by
  rw [tableWords,tableWords,MainTheory.PermutationFrameBridge.innerC_permAct]
  exact encoder_orthonormal _ _ _ j k

theorem table_gate (r : Fin 4) (theta : ℝ) (j : Fin 2) :
    MainTheory.Gate.gate (-1) (fun i => (records r i : ZMod 2)) (tableWords r theta j)=
      (if j=0 then (1 : ℂ) else -1) • tableWords r theta j := by
  rw [← table_angles r]
  unfold tableWords
  rw [gate_permAct,encoder_gate]
  rfl

end
end MainTheory.SplitFamilyTableCertification
