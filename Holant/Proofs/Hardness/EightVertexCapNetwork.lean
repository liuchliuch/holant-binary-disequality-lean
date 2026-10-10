import Holant.Proofs.Hardness.GeneralCancellationCapPin
import Holant.Complexity.BinaryInterpolation.Chains.Network

/-! A literal original-M cap attached to port zero of a second original M.
Both vertices retain their original four ordered ports. The cap's first
boundary is the new port zero; its second boundary joins the original port
zero by X. There are exactly two original vertices and two native X edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCapNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace Cap
export GeneralCancellationCapPin (Choice network oriented full_table)
end Cap
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex tensor_denote reindex_denote)
end Chain
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K]

/-- Old [cap0,cap1,M0,M1,M2,M3] becomes [cap1,M0,cap0,M1,M2,M3]. -/
def order : Equiv.Perm (Fin 6) where
  toFun := ![2,0,1,3,4,5]
  invFun := ![1,2,0,3,4,5]
  left_inv := by decide
  right_inv := by decide

def network (M : Signature K 4) (k : Cap.Choice) : Network K 4 :=
  (Chain.reindex (Chain.tensor (Cap.network M k) (Network.corolla M)) order).contract
    Signature.disequality

def output (M : Signature K 4) (k : Cap.Choice) : Signature K 4 := fun t=>
  (if t 0 then (Cap.oriented M k).2 else (Cap.oriented M k).1)*M t

/-- Derived from the complete contraction sum, including both orientations. -/
theorem denote (M : Signature K 4) (he : EvenSupport M) (k : Cap.Choice) :
    (network M k).denote=output M k := by
  rw [network,Network.denote_contract,Chain.reindex_denote,Chain.tensor_denote,
    Cap.full_table M he k,Network.denote_corolla]
  funext t
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply]
  have hw (u : Bool) :
      (fun i : Fin 4 => (Fin.cons u (Fin.cons (!u) t) : Fin 6→Bool)
        (order (Fin.natAdd 2 i)))=![!u,t 1,t 2,t 3] := by
    funext i
    fin_cases i <;> rfl
  change _*M (fun i=>(Fin.cons false (Fin.cons true t) : Fin 6→Bool)
      (order (Fin.natAdd 2 i)))+
    _*M (fun i=>(Fin.cons true (Fin.cons false t) : Fin 6→Bool)
      (order (Fin.natAdd 2 i)))=_
  have hf := hw false
  have ht := hw true
  simp only [Bool.not_false] at hf
  simp only [Bool.not_true] at ht
  rw [hf,ht]
  change (if t 0 then (Cap.oriented M k).2 else 0)*M ![true,t 1,t 2,t 3]+
    (if t 0 then 0 else (Cap.oriented M k).1)*M ![false,t 1,t 2,t 3]=_
  cases h0 : t 0
  · have ht : ![false,t 1,t 2,t 3]=t := by
      funext i; fin_cases i <;> simp [h0]
    simp [output,h0,ht]
  · have ht : ![true,t 1,t 2,t 3]=t := by
      funext i; fin_cases i <;> simp [h0]
    simp [output,h0,ht]

def labels (M : Signature K 4) (k : Cap.Choice) :
    Labelling (network M k).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity v := by
    change 4=(Network.tensorFinite (Cap.network M k) (Network.corolla M)).arity
      (finSumFinEquiv.symm v)
    cases finSumFinEquiv.symm v <;> rfl
  edge _ := 0

abbrev template (M : Signature K 4) (k : Cap.Choice) := (labels M k).template

theorem valid (M : Signature K 4) (k : Cap.Choice) :
    (template M k).WellFormed 1 1 (fun _=>4) := (labels M k).wellFormed

theorem counts (M : Signature K 4) (k : Cap.Choice) :
    (template M k).boundary=4 ∧ (template M k).vertices.length=2 ∧
      (template M k).edges.length=2 := by
  exact ⟨rfl,(labels M k).vertices_length,(labels M k).edges_length⟩

/-- Cap loop endpoints retain their orientation; attachment adds edge zero.
The sole old cap boundary zero becomes the new ordered boundary zero. -/
def capEndpoint : LocalEndpoint → LocalEndpoint
  | .inl n => if n=0 then .inl 0 else .inr (0,false)
  | .inr (e,b) => .inr (e+1,b)

/-- All twelve literal cap choices preserve both original local port lists. -/
theorem records (M : Signature K 4) (k : Cap.Choice) :
    (template M k).vertices=
      [(0,(GeneralCancellationCapPin.ports k).map capEndpoint),
       (0,[.inr (0,true),.inl 1,.inl 2,.inl 3])] ∧
    (template M k).edges=[0,0] := by
  rcases k with ⟨c,rev⟩
  fin_cases c <;> cases rev <;> exact ⟨rfl,rfl⟩

theorem template_actual (M : Signature K 4) (k : Cap.Choice) :
    ((template M k).network (valid M k) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=(network M k).denote := by
  apply Labelling.denote_template_of_labels (labels M k) _ _
    (network M k).vertex (network M k).edge
  · intro v t
    change Fin 2 at v
    fin_cases v <;> rfl
  · intro e a b
    change Fin 2 at e
    fin_cases e <;> rfl

theorem template_denote (M : Signature K 4) (he : EvenSupport M) (k : Cap.Choice) :
    ((template M k).network (valid M k) (fun _ : Fin 1=>M)
      (fun _ : Fin 1=>Signature.disequality)).denote=output M k := by
  rw [template_actual,denote M he]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCapNetwork
