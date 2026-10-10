import Holant.ReedMuller.SupportReconstruction.SliceCode
import Holant.ReedMuller.FlatNetwork.Parity

/-! Exact weight of the source parity-lift slice, hence divisibility by four. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant.ReedMuller.LowArity Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.FlatNetwork
open scoped BigOperators
variable {n r : ℕ} {i j : Fin n}

 def slicePorts (p : (Fin r × Bool) ≃ Remaining i j) (hij : i≠j) :
    (Bool ⊕ (Fin r × Bool)) ≃ Fin n where
  toFun z := Sum.elim (fun b=>if b then j else i) (fun eb=>(p eb).val) z
  invFun k := if hi : k=i then .inl false else if hj : k=j then .inl true else .inr (p.symm ⟨k,hi,hj⟩)
  left_inv z := by
    rcases z with b | eb
    · cases b <;> simp [Ne.symm hij]
    · simp [(p eb).property.1,(p eb).property.2]
  right_inv k := by
    by_cases hi : k=i
    · subst k; simp
    · by_cases hj : k=j
      · subst k; simp [hi]
      · simp [hi,hj]

 theorem sliceWord_weight (p : (Fin r × Bool) ≃ Remaining i j) (hij : i≠j) (t : BinaryVector r) :
    binaryWeight (sliceWord p t)=2*binaryWeight t+2*(if (∑e,t e)=1 then 1 else 0 : ℕ) := by
  classical
  unfold binaryWeight
  rw [Finset.card_filter,←(slicePorts p hij).sum_comp]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,slicePorts,
    Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr,Bool.true_eq_false,Bool.false_eq_true,ite_true,ite_false,
    sliceWord_left,sliceWord_right,sliceWord_port]
  rw [Finset.sum_add_distrib,Finset.card_filter]
  omega

 theorem sliceWord_weight_dvd_four (p : (Fin r × Bool) ≃ Remaining i j) (hij : i≠j) (t : BinaryVector r) :
    4∣binaryWeight (sliceWord p t) := by
  have hpar : (∑e,t e)=(binaryWeight t:ZMod 2) := by rw [cast_binaryWeight,dot_self]
  rcases Nat.even_or_odd (binaryWeight t) with ⟨m,hm⟩ | ⟨m,hm⟩
  · have hz : (∑e,t e)=0 := by rw [hpar,hm,Nat.cast_add]; exact add_self_zero _
    rw [sliceWord_weight p hij t,hz]
    norm_num
    exact ⟨m,by omega⟩
  · have he : binaryWeight t=m+m+1 := by omega
    have hz : (∑e,t e)=1 := by
      rw [hpar,he,Nat.cast_add,Nat.cast_add,Nat.cast_one,add_self_zero,zero_add]
    rw [sliceWord_weight p hij t,hz]
    norm_num
    exact ⟨m+1,by omega⟩

 theorem sliceCode_weight_dvd_four (p : (Fin r × Bool) ≃ Remaining i j) (hij : i≠j)
    (x : BinaryVector n) (hx : x∈sliceCode p) : 4∣binaryWeight x := by
  obtain ⟨t,rfl⟩ := hx
  exact sliceWord_weight_dvd_four p hij t

 theorem sliceWord_singleton_weight (p : (Fin r × Bool) ≃ Remaining i j) (hij : i≠j) (e : Fin r) :
    binaryWeight (sliceWord p (Pi.single e 1))=4 := by
  rw [sliceWord_weight p hij]
  simp [binaryWeight,Pi.single_apply,eq_comm]
  have hs : (Finset.univ.filter (fun x : Fin r=>e=x))={e} := by ext x; simp [eq_comm]
  rw [hs]
  rfl

end Holant.ReedMuller.SupportReconstruction
