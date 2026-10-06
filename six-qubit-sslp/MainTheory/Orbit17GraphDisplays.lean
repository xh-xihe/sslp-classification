import MainTheory.Orbit17ConjugatePhases
set_option autoImplicit false
namespace MainTheory.Orbit17GraphDisplays

/-- Four-vertex hafnian of the manuscript's complex edge labels. -/
def H (c : Fin 6 → Fin 6 → ℂ) (i j k l : Fin 6) : ℂ :=
  c i j*c k l+c i k*c j l+c i l*c j k

theorem normalized_nonneighbor_pair_sum (c : Fin 6 → Fin 6 → ℂ)
    (v u r s : Fin 6) (hvu : c v u=0) (hvr : c v r=1) (hvs : c v s=1) :
    H c v u r s=c u r+c u s := by
  simp only [H,hvu,hvr,hvs]
  ring

theorem isolated_matching_value (c : Fin 6 → Fin 6 → ℂ)
    (v a u w : Fin 6) (hva : c v a=1) (hvu : c v u=0) (hvw : c v w=0)
    (huw : c u w≠0) : H c v a u w=c u w ∧ H c v a u w≠0 := by
  have h : H c v a u w=c u w := by
    simp only [H,hva,hvu,hvw,one_mul,zero_mul,add_zero]
  exact ⟨h,h ▸ huw⟩

theorem normalized_universal_triangle (c : Fin 6 → Fin 6 → ℂ)
    (v i j k : Fin 6) (hvi : c v i=1) (hvj : c v j=1) (hvk : c v k=1) :
    H c v i j k=c i j+c i k+c j k := by
  simp only [H,hvi,hvj,hvk,one_mul]
  ring

end MainTheory.Orbit17GraphDisplays
