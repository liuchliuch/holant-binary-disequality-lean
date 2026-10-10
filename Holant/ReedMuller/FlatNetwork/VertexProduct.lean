import Holant.ReedMuller.FlatNetwork.NamedPorts

/-! The actual product of all vertex tables, including an empty vertex set,
is flat on the direct sum of their true self-dual support codes. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {a : V → ℕ} {n : ℕ}

def componentWord (e : (Σ v,Fin (a v)) ≃ Fin n) (v : V) (x : BinaryVector n) : BinaryVector (a v) :=
  fun i => x (e ⟨v,i⟩)

def vertexCode (e : (Σ v,Fin (a v)) ≃ Fin n) (D : ∀ v,BinaryCode (a v)) : BinaryCode n where
  carrier := {x | ∀ v,componentWord e v x∈D v}
  zero_mem' := fun v => (D v).zero_mem
  add_mem' := fun hx hy v => (D v).add_mem (hx v) (hy v)
  smul_mem' := fun c _ hx v => (D v).smul_mem c (hx v)

theorem dot_components (e : (Σ v,Fin (a v)) ≃ Fin n) (x y : BinaryVector n) :
    dot x y=∑ v,dot (componentWord e v x) (componentWord e v y) := by
  rw [dot,←e.sum_comp]
  exact Fintype.sum_sigma _

def singleComponent (e : (Σ v,Fin (a v)) ≃ Fin n) (v : V) (y : BinaryVector (a v)) : BinaryVector n :=
  fun i => (Pi.single (M := fun w : V => BinaryVector (a w)) v y (e.symm i).1) (e.symm i).2

theorem component_single (e : (Σ v,Fin (a v)) ≃ Fin n) (v w : V) (y : BinaryVector (a v)) :
    componentWord e w (singleComponent e v y)=Pi.single (M := fun w : V => BinaryVector (a w)) v y w := by
  funext i
  dsimp only [componentWord,singleComponent]
  rw [e.symm_apply_apply]

theorem vertexCode_selfDual (e : (Σ v,Fin (a v)) ≃ Fin n) (D : ∀ v,BinaryCode (a v))
    (hD : ∀ v,SelfDual (D v)) : SelfDual (vertexCode e D) := by
  intro x
  constructor
  · intro hx y hy
    rw [dot_components e]
    apply Finset.sum_eq_zero
    intro v _
    exact (hD v _).mp (hx v) _ (hy v)
  · intro hx v
    apply (hD v _).mpr
    intro y hy
    have hm : singleComponent e v y∈vertexCode e D := by
      intro w
      rw [component_single]
      by_cases hw : w=v
      · subst w;simpa using hy
      · simpa [Pi.single_eq_of_ne hw] using (D w).zero_mem
    have H := hx _ hm
    rw [dot_components e] at H
    simp only [component_single] at H
    have hs : (∑ w,dot (componentWord e w x) (Pi.single (M := fun w : V => BinaryVector (a w)) v y w))=dot (componentWord e v x) y := by
      rw [Finset.sum_eq_single v]
      · simp
      · intro w _ hw
        simp [Pi.single_eq_of_ne hw,dot]
      · simp
    rwa [hs] at H

def vertexProduct (f : ∀ v,Signature ℂ (a v)) : Tensor ℂ (Σ v,Fin (a v)) :=
  fun x => ∏ v,f v (fun i => x ⟨v,i⟩)

theorem vertexProduct_flat (f : ∀ v,Signature ℂ (a v)) (hf : ∀ v,Flat (f v)) :
    FlatTensor (vertexProduct f) := by
  choose c b D hD he using hf
  let e := Fintype.equivFin (Σ v,Fin (a v))
  let shift : BinaryVector (Fintype.card (Σ v,Fin (a v))) := fun i => b (e.symm i).1 (e.symm i).2
  refine ⟨_,e,∏ v,c v,shift,vertexCode e D,vertexCode_selfDual e D hD,?_⟩
  funext x
  have hm : ((fun i => bit (x i)-shift i)∈vertexCode e D) ↔
      ∀ v,(fun i => bit (x (e ⟨v,i⟩))-b v i)∈D v := by
    change (∀ v,componentWord e v (fun i => bit (x i)-shift i)∈D v) ↔ _
    have hh : (fun v => componentWord e v (fun i => bit (x i)-shift i))=
        fun v i => bit (x (e ⟨v,i⟩))-b v i := by
      funext v i
      change bit (x (e ⟨v,i⟩))-b (e.symm (e ⟨v,i⟩)).1 (e.symm (e ⟨v,i⟩)).2=_
      rw [e.symm_apply_apply]
    apply forall_congr'
    intro v
    rw [congrFun hh v]
  simp only [Tensor.reindex,vertexProduct,he,flatSignature]
  rw [hm]
  by_cases h : ∀ v,(fun i => bit (x (e ⟨v,i⟩))-b v i)∈D v
  · simp [h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨v,hv⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    exact if_neg hv

end
end Holant.ReedMuller.FlatNetwork
