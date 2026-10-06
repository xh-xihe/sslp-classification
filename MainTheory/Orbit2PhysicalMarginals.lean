import MainTheory.Orbit2ActiveProjectorRank

/-! Actual reduced density matrices and the two rank-four active parity blocks. -/

namespace MainTheory.Orbit2PhysicalMarginals

noncomputable section

open Orbit2 Orbit2.TensorPauli
open scoped BigOperators
open ComplexOrder

def activeWord (V : Encoder) (j : Fin 2) : Matrix ActiveBits ActiveBits ℂ :=
  fun x y => ∑ b : SpectatorBits,
    V.tensorMatrix (joinBits b x) j*star (V.tensorMatrix (joinBits b y) j)

def active (V : Encoder) : Matrix ActiveBits ActiveBits ℂ :=
  (1/2 : ℂ) • (activeWord V 0+activeWord V 1)

def spectatorWord (V : Encoder) (j : Fin 2) : Matrix SpectatorBits SpectatorBits ℂ :=
  fun b c => ∑ x : ActiveBits,
    V.tensorMatrix (joinBits b x) j*star (V.tensorMatrix (joinBits c x) j)

def spectator (V : Encoder) : Matrix SpectatorBits SpectatorBits ℂ :=
  (1/2 : ℂ) • (spectatorWord V 0+spectatorWord V 1)

def parityProjection (V : Encoder) (j : Fin 2) : Matrix ActiveBits ActiveBits ℂ :=
  V.schmidtFrame j*(V.schmidtFrame j).conjTranspose

def D : Matrix ActiveBits ActiveBits ℂ := operator (fun _ => 3)

theorem active_word_projector (V : Encoder) (j : Fin 2) :
    activeWord V j=(1/4 : ℂ) • parityProjection V j := by
  ext x y
  simp only [activeWord,parityProjection,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Encoder.schmidtFrame,Matrix.smul_apply,smul_eq_mul,star_mul,star_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem active_density (V : Encoder) : active V=(1/8 : ℂ) • V.activeProjector := by
  rw [active,active_word_projector,active_word_projector,V.activeProjector_frames]
  ext x y
  simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,parityProjection]
  ring

theorem spectator_word_flat (V : Encoder) (j : Fin 2) :
    spectatorWord V j=(1/4 : ℂ) • (1 : Matrix SpectatorBits SpectatorBits ℂ) := by
  ext b c
  have h := congrArg (fun M => M c b) (V.schmidtFrame_cross j j)
  simp only [ite_true,Matrix.mul_apply,Matrix.conjTranspose_apply,Encoder.schmidtFrame,
    Matrix.one_apply,star_mul,star_ofNat] at h
  have he : (∑ x : ActiveBits,star (2*V.tensorMatrix (joinBits c x) j)*
      (2*V.tensorMatrix (joinBits b x) j))=4*spectatorWord V j b c := by
    simp only [spectatorWord,star_mul,star_ofNat,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp only [star_mul,star_ofNat] at he
  rw [he] at h
  simp only [Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  by_cases hb : b=c
  · subst c
    simp only [ite_true] at h ⊢
    linear_combination h/4
  · simp only [hb,Ne.symm hb,if_false] at h ⊢
    linear_combination h/4

theorem spectator_density (V : Encoder) :
    spectator V=(1/4 : ℂ) • (1 : Matrix SpectatorBits SpectatorBits ℂ) := by
  rw [spectator,spectator_word_flat,spectator_word_flat]
  ext b c
  simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul]
  ring

theorem parity_rank_four (V : Encoder) (j : Fin 2) : (parityProjection V j).rank=4 := by
  rw [parityProjection,Matrix.rank_self_mul_conjTranspose,
    ← Matrix.rank_conjTranspose_mul_self,V.schmidtFrame_cross,if_pos rfl,Matrix.rank_one]
  norm_num [SpectatorBits]

theorem parity_left (V : Encoder) (j : Fin 2) :
    D*parityProjection V j=(if j=0 then (1 : ℂ) else -1) • parityProjection V j := by
  rw [parityProjection,← Matrix.mul_assoc]
  change (operator (fun _ : Fin 4 => 3)*V.schmidtFrame j)*(V.schmidtFrame j).conjTranspose=_
  rw [V.schmidtFrame_parity,Matrix.smul_mul]

theorem parity_right (V : Encoder) (j : Fin 2) :
    parityProjection V j*D=(if j=0 then (1 : ℂ) else -1) • parityProjection V j := by
  have h := congrArg Matrix.conjTranspose (parity_left V j)
  have hP : (parityProjection V j).conjTranspose=parityProjection V j := by
    simp [parityProjection,Matrix.conjTranspose_mul]
  have hD : D.conjTranspose=D := operator_hermitian _
  simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_smul,hP,hD] at h
  by_cases hj : j=0
  · simpa only [hj,if_true,star_one] using h
  · simpa only [hj,if_false,star_one,star_neg] using h

theorem active_commutes (V : Encoder) : D*V.activeProjector=V.activeProjector*D := by
  rw [V.activeProjector_frames]
  change D*(parityProjection V 0+parityProjection V 1)=
    (parityProjection V 0+parityProjection V 1)*D
  rw [Matrix.mul_add,Matrix.add_mul,parity_left,parity_left,parity_right,parity_right]

theorem literal_parity_block (V : Encoder) (j : Fin 2) :
    ((1/2 : ℂ) • (1+(if j=0 then (1 : ℂ) else -1) • D))*V.activeProjector=
      parityProjection V j := by
  rw [Matrix.smul_mul,Matrix.add_mul,Matrix.one_mul,Matrix.smul_mul,
    V.activeProjector_frames,Matrix.mul_add]
  change (1/2 : ℂ) • ((parityProjection V 0+parityProjection V 1)+
    (if j=0 then (1 : ℂ) else -1) • (D*parityProjection V 0+D*parityProjection V 1))=_
  rw [parity_left,parity_left]
  fin_cases j <;> ext x y <;>
    norm_num [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul] <;> ring

theorem literal_parity_rank (V : Encoder) (j : Fin 2) :
    (((1/2 : ℂ) • (1+(if j=0 then (1 : ℂ) else -1) • D))*V.activeProjector).rank=4 := by
  rw [literal_parity_block,parity_rank_four]

end

end MainTheory.Orbit2PhysicalMarginals
