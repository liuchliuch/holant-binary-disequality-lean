import Holant.ReedMuller.RadonAccess.Directions
import Holant.ReedMuller.CharacterFlat.Basic

/-! A nonconstant coefficient-square table on a parity sector has an actual
noncentral Fourier witness. A finite RM coordinate program moves that witness
to weight one or two, with no support or normalization assumption. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineFourier
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def transform (f : BinaryVector n→ℂ) (v : BinaryVector n) : ℂ := ∑x,sign (dot v x)*f x

theorem character_sum (v : BinaryVector n) :
    (∑x : BinaryVector n,sign (dot v x))=if v=0 then (2:ℂ)^n else 0 := by
  by_cases zero : v=0
  · subst v
    simp [dot,sign,intSign,Fintype.card_fun]
  · rw [if_neg zero]
    obtain ⟨i,hi⟩ : ∃i,v i≠0 := by by_contra! none;exact zero (funext none)
    have one : v i=1 := by revert hi;generalize v i=a;fin_cases a <;> simp
    let F : BinaryVector n→ℂ := fun x=>sign (dot v x)
    have flip (x : BinaryVector n) : F (x+unitWord i)= -F x := by
      dsimp [F]
      rw [dot_add_right,dot_unit_right,one,sign_add,sign_one]
      ring
    have sum := Equiv.sum_comp (Equiv.addRight (unitWord i)) F
    change (∑x : BinaryVector n,F (x+unitWord i))=∑x : BinaryVector n,F x at sum
    simp only [flip,Finset.sum_neg_distrib] at sum
    have twice : (2:ℂ)*(∑x : BinaryVector n,F x)=0 := by linear_combination -sum
    exact (mul_eq_zero.mp twice).resolve_left (by norm_num)

theorem kernel_orthogonal (x y : BinaryVector n) :
    (∑v : BinaryVector n,sign (dot x v)*sign (dot v y))=
      if x=y then (2:ℂ)^n else 0 := by
  have term (v : BinaryVector n) : sign (dot x v)*sign (dot v y)=sign (dot v (x+y)) := by
    rw [dot_add_right,sign_add,dot_comm x v]
  simp_rw [term,dot_comm _ (x+y)]
  rw [character_sum]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    exact (Holant.ReedMuller.FlatNetwork.add_eq_zero_iff (x i) (y i)).mp (congrFun h i)
  · rintro rfl
    funext i
    exact add_self_zero (x i)

theorem inversion (f : BinaryVector n→ℂ) (x : BinaryVector n) :
    transform (transform f) x=(2:ℂ)^n*f x := by
  unfold transform
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _=∑z : BinaryVector n,(∑v : BinaryVector n,sign (dot x v)*sign (dot v z))*f z := by
      apply Finset.sum_congr rfl
      intro z _
      simp only [Finset.sum_mul,mul_assoc]
    _=∑z : BinaryVector n,(if x=z then (2:ℂ)^n else 0)*f z := by simp_rw [kernel_orthogonal]
    _=_ := by simp [ite_mul]

theorem constant_on_parity (f : BinaryVector n→ℂ)
    (vanishing : ∀v : BinaryVector n,v≠0→v≠ones n→transform f v=0) :
    ∀x y : BinaryVector n,dot (ones n) x=dot (ones n) y→f x=f y := by
  intro x y parity
  apply mul_left_cancel₀ (pow_ne_zero n (by norm_num : (2:ℂ)≠0))
  rw [←inversion f x,←inversion f y]
  unfold transform
  apply Finset.sum_congr rfl
  intro v _
  by_cases vzero : v=0
  · subst v
    simp [dot]
  by_cases vones : v=ones n
  · subst v
    rw [dot_comm x,dot_comm y,parity]
  · have hz := vanishing v vzero vones
    change sign (dot x v)*transform f v=sign (dot y v)*transform f v
    rw [hz,mul_zero,mul_zero]

theorem noncentral_witness (f : BinaryVector n→ℂ)
    (bad : ¬∀x y : BinaryVector n,dot (ones n) x=dot (ones n) y→f x=f y) :
    ∃v : BinaryVector n,v≠0 ∧ v≠ones n ∧ transform f v≠0 := by
  by_contra! none
  exact bad (constant_on_parity f none)

private theorem reduce_weight_aux (w : ℕ) :
    ∀v : BinaryVector n,binaryWeight v=w→0<w→w<n→
      ∃p : GenerationProgram n,binaryWeight (p.word v)=1 ∨ binaryWeight (p.word v)=2 := by
  induction w using Nat.strong_induction_on with
  | h w ih =>
    intro v weight positive proper
    by_cases small : w≤2
    · refine ⟨[],?_⟩
      change binaryWeight v=1 ∨ binaryWeight v=2
      omega
    obtain ⟨s,hs,_isotropic,drop⟩ := exists_weightFour_reduction v (by omega) (by omega)
    have smaller : binaryWeight (transvection s v)<w := by omega
    obtain ⟨p,hp⟩ := ih _ smaller (transvection s v) rfl (by omega) (by omega)
    refine ⟨p++[.tau s hs],?_⟩
    simpa only [GenerationProgram.word_append,GenerationProgram.word,GenerationGate.applyWord] using hp

theorem coordinate_reduction (v : BinaryVector n) (zero : v≠0) (one : v≠ones n) :
    ∃p : GenerationProgram n,binaryWeight (p.word v)=1 ∨ binaryWeight (p.word v)=2 :=
  reduce_weight_aux (binaryWeight v) v rfl ((binaryWeight_pos_iff v).mpr zero)
    ((binaryWeight_lt_iff v).mpr one)

theorem transform_action (p : GenerationProgram n) (f : BinaryVector n→ℂ) (v : BinaryVector n) :
    transform (fun x=>f (p.inverse.word x)) (p.word v)=transform f v := by
  unfold transform
  rw [←Equiv.sum_comp p.orthogonalMap.linear.toEquiv
    (fun x=>sign (dot (p.word v) x)*f (p.inverse.word x))]
  have eval (x : BinaryVector n) : p.orthogonalMap.linear.toEquiv x=p.word x :=
    GenerationProgram.orthogonalMap_apply p x
  simp only [eval,GenerationProgram.word_isometry,GenerationProgram.word_inverse]

theorem local_fourier_witness (f : BinaryVector n→ℂ)
    (bad : ¬∀x y : BinaryVector n,dot (ones n) x=dot (ones n) y→f x=f y) :
    ∃p : GenerationProgram n,∃v : BinaryVector n,
      (binaryWeight v=1 ∨ binaryWeight v=2) ∧ transform (fun x=>f (p.inverse.word x)) v≠0 := by
  obtain ⟨v,zero,one,live⟩ := noncentral_witness f bad
  obtain ⟨p,small⟩ := coordinate_reduction v zero one
  exact ⟨p,p.word v,small,by rwa [transform_action]⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineFourier
end
