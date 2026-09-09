import MainTheory.Orbit9EnumeratorDisplays
import MainTheory.Generated.OrbitTableNumericData
import SixQubit.Orbit21Enum

set_option autoImplicit false

namespace MainTheory.Orbit21EnumeratorDisplays

open SS.MacWilliams MainTheory.Generated.OrbitTableNumericData

theorem record : paperQ 20=4 ∧ paperM 20=2 ∧
    SixQubit.Orbit21Cert.av=![1,1,1,2,2,3] := ⟨rfl,rfl,rfl⟩

theorem parity : ∀ x : SS.BitString 6,
    (SS.weight SixQubit.Orbit21Cert.av x=0 ∨ SS.weight SixQubit.Orbit21Cert.av x=2) →
    xor (xor (xor (x 0) (x 1)) (x 2)) (x 5)=false := by decide +kernel

theorem normalized_enumerators (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 2 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hcode : SS.HasDistance ![c,d] 3) :
    (fun j : Fin 7 => Aco ![c,d] j/4)=![1,0,1,0,11,16,3] ∧
    (fun j : Fin 7 => Bco ![c,d] j/4)=![1,0,1,24,35,40,27] := by
  obtain ⟨hA,hB⟩ := SixQubit.Orbit21Enum.enumerator_pair_unique_fiber c d hc hd hnc hnd hcode
  exact MainTheory.Orbit9EnumeratorDisplays.normalized_enumerators ![c,d] hA hB

theorem A2_lower (psi : Fin 2 → SS.State 6 ℂ)
    (hc : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 0 → psi 0 x=0)
    (hd : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 2 → psi 1 x=0)
    (hnorm : ∀ i,SS.innerC (psi i) (psi i)=1) (hcode : SS.HasDistance psi 3) :
    1 ≤ Aco psi 2/4 := by
  have h := SixQubit.Orbit21Farkas.four_le_Aco_two psi hc hd hnorm hcode
  linarith

theorem first_three (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight SixQubit.Orbit21Cert.av x ≠ 2 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hcode : SS.HasDistance ![c,d] 3) :
    Aco ![c,d] 1/4=0 ∧ Aco ![c,d] 2/4=1 ∧ Aco ![c,d] 3/4=0 := by
  have h := (normalized_enumerators c d hc hd hnc hnd hcode).1
  exact ⟨congrFun h 1,congrFun h 2,congrFun h 3⟩

theorem attained : ∃ c d : SS.State 6 ℂ,
    SS.innerC c c=1 ∧ SS.innerC d d=1 ∧ SS.HasDistance ![c,d] 3 ∧
    (fun j : Fin 7 => Aco ![c,d] j/4)=![1,0,1,0,11,16,3] ∧
    (fun j : Fin 7 => Bco ![c,d] j/4)=![1,0,1,24,35,40,27] := by
  obtain ⟨hA,hB⟩ := SixQubit.Orbit21Enum.enumerator_pair_attained
  exact ⟨SixQubit.Orbit21Real.w0,SixQubit.Orbit21Real.w1,
    SixQubit.Orbit21Real.w0_normalized,SixQubit.Orbit21Real.w1_normalized,
    SixQubit.Orbit21Real.is_code,
    MainTheory.Orbit9EnumeratorDisplays.normalized_enumerators _ hA hB⟩

end MainTheory.Orbit21EnumeratorDisplays
