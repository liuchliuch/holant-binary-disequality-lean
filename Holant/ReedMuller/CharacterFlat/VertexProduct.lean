import Holant.ReedMuller.CharacterFlat.NamedPorts
import Holant.ReedMuller.FlatNetwork.VertexProduct

/-! The actual product of signed vertex tables has the direct sum support and
sum character, including empty and nullary collections of vertices. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {a : V → ℕ} {n : ℕ}

theorem sign_finset_sum {I : Type*} (s : Finset I) (f : I → ZMod 2) :
    sign (∑ i ∈ s,f i)=∏ i ∈ s,sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,sign_add,ih]

def componentLinear (e : (Σ v,Fin (a v)) ≃ Fin n) (v : V) :
    BinaryVector n →ₗ[ZMod 2] BinaryVector (a v) where
  toFun := componentWord e v
  map_add' := by intros;rfl
  map_smul' := by intros;rfl

@[simp] theorem componentLinear_apply (e : (Σ v,Fin (a v)) ≃ Fin n) (v : V)
    (x : BinaryVector n) : componentLinear e v x=componentWord e v x := rfl

theorem vertexProduct_nonzeroFlat (f : ∀ v,Signature ℂ (a v))
    (hf : ∀ v,NonzeroFlat (f v)) : CharacterTensor (vertexProduct f) := by
  choose c b D ell hD he using hf
  let e := Fintype.equivFin (Σ v,Fin (a v))
  let shift : BinaryVector (Fintype.card (Σ v,Fin (a v))) := fun i => b (e.symm i).1 (e.symm i).2
  refine ⟨_,e,∏ v,c v,shift,vertexCode e D,∑ v,(ell v).comp (componentLinear e v),
    vertexCode_selfDual e D hD,?_⟩
  funext x
  have hm : (vectorWord x-shift∈vertexCode e D) ↔
      ∀ v,(fun i => bit (x (e ⟨v,i⟩))-b v i)∈D v := by
    change (∀ v,componentWord e v (vectorWord x-shift)∈D v) ↔ _
    apply forall_congr'
    intro v
    have hh : componentWord e v (vectorWord x-shift)=fun i => bit (x (e ⟨v,i⟩))-b v i := by
      funext i
      change bit (x (e ⟨v,i⟩))-b (e.symm (e ⟨v,i⟩)).1 (e.symm (e ⟨v,i⟩)).2=_
      rw [e.symm_apply_apply]
    rw [hh]
  simp only [Tensor.reindex,vertexProduct,he,signature,value]
  rw [hm]
  by_cases h : ∀ v,(fun i => bit (x (e ⟨v,i⟩))-b v i)∈D v
  · rw [if_pos h]
    have hv : ∀ v,vectorWord (fun i => x (e ⟨v,i⟩))-b v∈D v := h
    simp only [hv,ite_true,LinearMap.sum_apply,LinearMap.comp_apply,componentLinear_apply]
    rw [sign_finset_sum,Units.coe_prod,Finset.prod_mul_distrib]
    rfl
  · rw [if_neg h]
    push_neg at h
    obtain ⟨v,hv⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    exact if_neg hv

 theorem vertexProduct_CFlat (f : ∀ v,Signature ℂ (a v)) (hf : ∀ v,CFlat (f v)) :
    CharacterTensorOrZero (vertexProduct f) := by
  classical
  by_cases hz : ∃ v,f v=0
  · obtain ⟨v,hv⟩ := hz
    left
    funext x
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [hv]
  · right
    apply vertexProduct_nonzeroFlat
    intro v
    exact (hf v).resolve_left (fun h => hz ⟨v,h⟩)

end
end Holant.ReedMuller.CharacterFlat
