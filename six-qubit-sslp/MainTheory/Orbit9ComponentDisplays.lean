import MainTheory.Orbit9ConnectedComponents

set_option autoImplicit false

namespace MainTheory.Orbit9ComponentDisplays

open SixQubit.Orbit9Universal MainTheory.Orbit9ConnectedComponents

noncomputable def m (c : SS.State 6 ℂ) (i j : Fin 6) : ℂ :=
  damp c i j*xamp c i*xamp c j

theorem pair_flip (c d : SS.State 6 ℂ) (H : FullKL c d) (i j k l : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    star (damp c i j)*camp d k l+star (damp c k l)*camp d i j+
      star (damp c i k)*camp d j l+star (damp c j l)*camp d i k+
      star (damp c i l)*camp d j k+star (damp c j k)*camp d i l=0 :=
  pairRow_all c d (pair_rows c d H.support0 H.support1 H.distance) i j k l
    hij hik hil hjk hjl hkl

theorem matrix_entry (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) (i j : Fin 6)
    (hi : i ∈ component c a) (hj : j ∈ component c a) : componentMatrix c d a i j=m c i j := by
  simp [componentMatrix,m,component_phase c d H a ha i hi,component_phase c d H a ha j hj]

theorem m_row (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) (i : Fin 6) (hi : i ∈ component c a) :
    (∑ j ∈ component c a,m c i j)=0 := component_m_row c d H a ha i hi

theorem m_hafnian (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) (i j k l : Fin 6)
    (hi : i ∈ component c a) (hj : j ∈ component c a)
    (hk : k ∈ component c a) (hl : l ∈ component c a)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    m c i j*m c k l+m c i k*m c j l+m c i l*m c j k=0 := by
  have h := componentMatrix_haf c d H a i j k l hij hik hil hjk hjl hkl
  simpa only [matrix_entry c d H a ha i j hi hj,matrix_entry c d H a ha k l hk hl,
    matrix_entry c d H a ha i k hi hk,matrix_entry c d H a ha j l hj hl,
    matrix_entry c d H a ha i l hi hl,matrix_entry c d H a ha j k hj hk] using h

theorem m_triangle (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) (i j k : Fin 6)
    (hi : i ∈ component c a) (hj : j ∈ component c a) (hk : k ∈ component c a)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    m c i j*m c i k+m c i j*m c j k+m c i k*m c j k=0 := by
  have h := SixQubit.Orbit9Matrix.triangle_relation (component_matrix_sys c d H a ha)
    i j k hij hik hjk
  simpa only [matrix_entry c d H a ha i j hi hj,matrix_entry c d H a ha i k hi hk,
    matrix_entry c d H a ha j k hj hk] using h

end MainTheory.Orbit9ComponentDisplays
