import MainTheory.Orbit33PrintedBlocks

/-! The unit vectors and phase quotients in the printed block argument.
Only positive norms and the two rank-one cross relations are used.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit33NormalizedPairs
open MainTheory.Orbit33PrintedBlocks
open scoped BigOperators
noncomputable section

def normSq (v : Fin 2 → ℂ) : ℝ := Complex.normSq (v 0)+Complex.normSq (v 1)
def square (v : Fin 2 → ℂ) : ℂ := v 0*star (v 0)+v 1*star (v 1)

theorem square_cast (v : Fin 2 → ℂ) : square v=(normSq v : ℂ) := by
  norm_num [square,normSq,Complex.normSq_eq_conj_mul_self]
  ring

theorem determinant_of_pair (u v p q : Fin 2 → ℂ) (r : ℝ) (hr : 0<r)
    (hn : normSq p=r) (h : mixed p v+mixed q u=0) : u 0*v 1-u 1*v 0=0 := by
  have hp : square p=(r : ℂ) := by rw [square_cast,hn]
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  have h10 := congrFun (congrFun h 1) 0
  have h11 := congrFun (congrFun h 1) 1
  simp only [mixed,Matrix.add_apply,Matrix.zero_apply] at h00 h01 h10 h11
  exact SixQubit.Block33.det_zero (u 0) (u 1) (v 0) (v 1) (p 0) (p 1) (q 0) (q 1) (r : ℂ)
    (by linear_combination h00) (by linear_combination h01)
    (by linear_combination h10) (by linear_combination h11) hp (by exact_mod_cast ne_of_gt hr)

theorem adjoint_pair (u v p q : Fin 2 → ℂ) (h : mixed p v+mixed q u=0) :
    mixed u q+mixed v p=0 := by
  ext r s
  have he := congrArg star (congrFun (congrFun h s) r)
  simp only [mixed,Matrix.add_apply,Matrix.zero_apply,star_add,star_mul',star_star,star_zero] at he ⊢
  linear_combination he

def normalized (v : Fin 2 → ℂ) (r : ℝ) : Fin 2 → ℂ := fun j => v j/(Real.sqrt r : ℂ)

theorem normalized_unit (v : Fin 2 → ℂ) (r : ℝ) (hr : 0<r) (hn : normSq v=r) :
    normSq (normalized v r)=1 := by
  have hs : Real.sqrt r*Real.sqrt r=r := Real.mul_self_sqrt (le_of_lt hr)
  simp only [normSq,normalized,Complex.normSq_div,Complex.normSq_ofReal]
  rw [hs,← add_div]
  change normSq v/r=1
  rw [hn,div_self (ne_of_gt hr)]

theorem factorization (u v : Fin 2 → ℂ) (r t : ℝ) (hr : 0<r) (ht : 0<t)
    (hn : normSq u=r) (hv : normSq v=t) (hdet : u 0*v 1-u 1*v 0=0) :
    ∃ a : ℂ, a≠0 ∧ v=a • normalized u r := by
  have hrC : (r : ℂ)≠0 := by exact_mod_cast ne_of_gt hr
  have hsC : (Real.sqrt r : ℂ)≠0 := by exact_mod_cast ne_of_gt (Real.sqrt_pos.2 hr)
  have hu : square u=(r : ℂ) := by rw [square_cast,hn]
  obtain ⟨h0,h1⟩ := SixQubit.Block33.scale (u 0) (u 1) (v 0) (v 1) (r : ℂ) hu hdet
  norm_num at h0 h1
  let a : ℂ := (star (u 0)*v 0+star (u 1)*v 1)/r*(Real.sqrt r : ℂ)
  have he : v=a • normalized u r := by
    funext j
    fin_cases j
    · change v 0=a*(u 0/(Real.sqrt r : ℂ))
      dsimp [a]
      field_simp [hrC,hsC]
      linear_combination h0
    · change v 1=a*(u 1/(Real.sqrt r : ℂ))
      dsimp [a]
      field_simp [hrC,hsC]
      linear_combination h1
  refine ⟨a,?_,he⟩
  intro ha
  have hz : v=0 := by rw [ha,zero_smul] at he; exact he
  have : normSq v=0 := by rw [hz]; norm_num [normSq]
  linarith

def R3 : Fin 3 → ℝ := ![3/10,1/5,1/5]
def next (i : Fin 2) : Fin 3 := ⟨i.val+1,by omega⟩

theorem positive_R3 : ∀ i, 0<R3 i := by intro i; fin_cases i <;> norm_num [R3]

theorem normalized_pairs (c d : Fin 3 → Fin 2 → ℂ)
    (hc : ∀ i, normSq (c i)=R3 i) (hd : ∀ i, normSq (d i)=R3 i)
    (hp : ∀ i : Fin 2, mixed (d 0) (c (next i))+mixed (d (next i)) (c 0)=0) :
    ∃ u v : Fin 2 → ℂ, ∃ a b : Fin 3 → ℂ,
      normSq u=1 ∧ normSq v=1 ∧
      (∀ i, a i≠0 ∧ b i≠0 ∧ c i=a i • u ∧ d i=b i • v) := by
  have dc : ∀ i, c 0 0*c i 1-c 0 1*c i 0=0 := by
    intro i
    fin_cases i
    · norm_num; ring
    · exact determinant_of_pair _ _ _ _ _ (positive_R3 0) (hd 0) (hp 0)
    · exact determinant_of_pair _ _ _ _ _ (positive_R3 0) (hd 0) (hp 1)
  have dd : ∀ i, d 0 0*d i 1-d 0 1*d i 0=0 := by
    intro i
    fin_cases i
    · norm_num; ring
    · exact determinant_of_pair _ _ _ _ _ (positive_R3 0) (hc 0) (adjoint_pair _ _ _ _ (hp 0))
    · exact determinant_of_pair _ _ _ _ _ (positive_R3 0) (hc 0) (adjoint_pair _ _ _ _ (hp 1))
  have fc := fun i => factorization (c 0) (c i) (R3 0) (R3 i) (positive_R3 0)
    (positive_R3 i) (hc 0) (hc i) (dc i)
  have fd := fun i => factorization (d 0) (d i) (R3 0) (R3 i) (positive_R3 0)
    (positive_R3 i) (hd 0) (hd i) (dd i)
  choose a ha he using fc
  choose b hb hf using fd
  exact ⟨normalized (c 0) (R3 0),normalized (d 0) (R3 0),a,b,
    normalized_unit _ _ (positive_R3 0) (hc 0),normalized_unit _ _ (positive_R3 0) (hd 0),
    fun i => ⟨ha i,hb i,he i,hf i⟩⟩

def gamma (a b : ℂ) : ℂ := b/star a

theorem coefficient_of_pair (u v : Fin 2 → ℂ) (hu : normSq u=1) (hv : normSq v=1)
    (a0 a1 b0 b1 : ℂ)
    (h : mixed (b0 • v) (a1 • u)+mixed (b1 • v) (a0 • u)=0) :
    b0*star a1+b1*star a0=0 := by
  have huc : ∃ r, u r≠0 := by
    by_contra hh
    push_neg at hh
    norm_num [normSq,hh] at hu
  have hvc : ∃ s, v s≠0 := by
    by_contra hh
    push_neg at hh
    norm_num [normSq,hh] at hv
  obtain ⟨r,hr⟩ := huc
  obtain ⟨s,hs⟩ := hvc
  have he := congrFun (congrFun h s) r
  norm_num [mixed,star_mul'] at he
  have hp : (b0*star a1+b1*star a0)*(v s*star (u r))=0 := by
    conv_lhs => norm_num
    linear_combination he
  exact (mul_eq_zero.mp hp).resolve_right (mul_ne_zero hs (star_ne_zero.2 hr))

theorem quotient_sign (a0 a1 b0 b1 : ℂ) (ha0 : a0≠0) (ha1 : a1≠0)
    (h : b0*star a1+b1*star a0=0) : gamma a1 b1 = -gamma a0 b0 := by
  unfold gamma
  rw [← neg_div]
  apply (div_eq_div_iff (star_ne_zero.2 ha1) (star_ne_zero.2 ha0)).2
  linear_combination h

theorem normalized_pairs_and_phases (c d : Fin 3 → Fin 2 → ℂ)
    (hc : ∀ i, normSq (c i)=R3 i) (hd : ∀ i, normSq (d i)=R3 i)
    (hp : ∀ i : Fin 2, mixed (d 0) (c (next i))+mixed (d (next i)) (c 0)=0) :
    ∃ u v : Fin 2 → ℂ, ∃ a b : Fin 3 → ℂ,
      normSq u=1 ∧ normSq v=1 ∧
      (∀ i, a i≠0 ∧ b i≠0 ∧ c i=a i • u ∧ d i=b i • v) ∧
      (∀ i : Fin 2, gamma (a (next i)) (b (next i)) = -gamma (a 0) (b 0)) ∧
      gamma (a 0) (b 0)≠0 := by
  obtain ⟨u,v,a,b,hu,hv,hf⟩ := normalized_pairs c d hc hd hp
  refine ⟨u,v,a,b,hu,hv,hf,?_,div_ne_zero (hf 0).2.1 (star_ne_zero.2 (hf 0).1)⟩
  intro i
  apply quotient_sign _ _ _ _ (hf 0).1 (hf (next i)).1
  apply coefficient_of_pair u v hu hv
  simpa only [(hf 0).2.2.1,(hf 0).2.2.2,(hf (next i)).2.2.1,(hf (next i)).2.2.2] using hp i

theorem physical_normalized_pairs (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ u v : Fin 2 → ℂ, ∃ a b : Fin 3 → ℂ,
      normSq u=1 ∧ normSq v=1 ∧
      (∀ i, a i≠0 ∧ b i≠0 ∧ CBlock c (near i)=a i • u ∧ DBlock d (near i)=b i • v) ∧
      (∀ i : Fin 2, gamma (a (next i)) (b (next i)) = -gamma (a 0) (b 0)) ∧
      gamma (a 0) (b 0)≠0 := by
  have hn := (physical_norms_and_reflection c d hc hd hnc hnd hkl).1
  apply normalized_pairs_and_phases
  · intro i
    have he := (hn (near i)).1
    fin_cases i <;> simpa [normSq,Fin.sum_univ_two,near,R,R3] using he
  · intro i
    have he := (hn (near i)).2
    fin_cases i <;> simpa [normSq,Fin.sum_univ_two,near,R,R3] using he
  · intro i
    have he := physical_rankone_pairs c d hc hd hkl i
    fin_cases i <;> simpa [near,next,pairIndex] using he

def inner (v w : Fin 2 → ℂ) : ℂ := star (v 0)*w 0+star (v 1)*w 1

theorem divided_cross (u v cf df : Fin 2 → ℂ) (a b : ℂ) (ha : a≠0)
    (h : inner cf (b • v)+inner (a • u) df=0) :
    gamma a b*inner cf v+inner u df=0 := by
  have hs : star a≠0 := star_ne_zero.2 ha
  have hf : b*inner cf v+star a*inner u df=0 := by
    norm_num [inner,star_mul'] at h ⊢
    linear_combination h
  have he : star a*(gamma a b*inner cf v+inner u df)=0 := by
    unfold gamma
    calc
      star a*(b/star a*inner cf v+inner u df)=
          (b/star a*star a)*inner cf v+star a*inner u df := by ring
      _ = 0 := by rw [div_mul_cancel₀ b hs]; exact hf
  exact (mul_eq_zero.mp he).resolve_left hs

theorem orthogonal_from_opposite (g A B : ℂ) (hg : g≠0)
    (h0 : g*A+B=0) (h1 : -g*A+B=0) : A=0 ∧ B=0 := by
  have hp : g*A=0 := by linear_combination (1/2 : ℂ)*h0-(1/2 : ℂ)*h1
  have hA := (mul_eq_zero.mp hp).resolve_left hg
  exact ⟨hA,by linear_combination h0-g*hA⟩

theorem physical_far_orthogonal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3)
    (u v : Fin 2 → ℂ) (a b : Fin 3 → ℂ)
    (hf : ∀ i, a i≠0 ∧ CBlock c (near i)=a i • u ∧ DBlock d (near i)=b i • v)
    (hg : gamma (a 0) (b 0)≠0)
    (hs : gamma (a 1) (b 1) = -gamma (a 0) (b 0)) (j : Fin 3) :
    inner (CBlock c (far j)) v=0 ∧ inner u (DBlock d (far j))=0 := by
  have h0 := physical_complete_cross c d hc hd hkl 0 j
  have h1 := physical_complete_cross c d hc hd hkl 1 j
  have he0 : inner (CBlock c (far j)) (DBlock d (near 0))+
      inner (CBlock c (near 0)) (DBlock d (far j))=0 := by
    norm_num [inner,Fin.sum_univ_two] at h0 ⊢
    linear_combination h0
  have he1 : inner (CBlock c (far j)) (DBlock d (near 1))+
      inner (CBlock c (near 1)) (DBlock d (far j))=0 := by
    norm_num [inner,Fin.sum_univ_two] at h1 ⊢
    linear_combination h1
  rw [(hf 0).2.1,(hf 0).2.2] at he0
  rw [(hf 1).2.1,(hf 1).2.2] at he1
  have hz0 := divided_cross u v _ _ (a 0) (b 0) (hf 0).1 he0
  have hz1 := divided_cross u v _ _ (a 1) (b 1) (hf 1).1 he1
  rw [hs] at hz1
  exact orthogonal_from_opposite _ _ _ hg hz0 hz1

structure Frame (c d : SS.State 6 ℂ) where
  u : Fin 2 → ℂ
  v : Fin 2 → ℂ
  a : Fin 3 → ℂ
  b : Fin 3 → ℂ
  unitU : normSq u=1
  unitV : normSq v=1
  factors : ∀ i, a i≠0 ∧ b i≠0 ∧ CBlock c (near i)=a i • u ∧ DBlock d (near i)=b i • v
  phaseSigns : ∀ i : Fin 2, gamma (a (next i)) (b (next i)) = -gamma (a 0) (b 0)
  phaseNonzero : gamma (a 0) (b 0)≠0
  orthogonalFar : ∀ j, inner (CBlock c (far j)) v=0 ∧ inner u (DBlock d (far j))=0

theorem physical_frame (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Nonempty (Frame c d) := by
  obtain ⟨u,v,a,b,hu,hv,hf,hs,hg⟩ := physical_normalized_pairs c d hc hd hnc hnd hkl
  refine ⟨⟨u,v,a,b,hu,hv,hf,hs,hg,?_⟩⟩
  intro j
  apply physical_far_orthogonal c d hc hd hkl u v a b _ hg _ j
  · exact fun i => ⟨(hf i).1,(hf i).2.2.1,(hf i).2.2.2⟩
  · simpa [next] using hs 0

end
end MainTheory.Orbit33NormalizedPairs
