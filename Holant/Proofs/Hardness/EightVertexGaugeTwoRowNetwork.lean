import Holant.Complexity.BinaryInterpolation.Chains.Network
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence

/-! Two original ordered four-port rows joined by two native X edges.
The optional crossing changes the incidence of the two right internal ports;
it never permutes or replaces either vertex label. This file supplies the
literal network, its complete contraction sum, and a two-label template. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex tensor_denote reindex_denote)
end Chain
variable {K : Type} [Field K]

/-- Old slots are [L0,L1,L2,L3,R0,R1,R2,R3]. New slots 0/1 and
2/3 are internal ends; new slots 4,...,7 are the ordered boundary. -/
def order (cross : Bool) : Equiv.Perm (Fin 8) where
  toFun := if cross then ![4,5,0,2,6,7,3,1] else ![4,5,0,2,6,7,1,3]
  invFun := if cross then ![2,7,3,6,0,1,4,5] else ![2,6,3,7,0,1,4,5]
  left_inv := by cases cross <;> decide
  right_inv := by cases cross <;> decide

def connect (L R : Network K 4) (cross : Bool) : Network K 4 :=
  ((Chain.reindex (Chain.tensor L R)
    (order cross)).contract Signature.disequality).contract Signature.disequality

def network (M N : Signature K 4) (cross : Bool) : Network K 4 :=
  connect (Network.corolla M) (Network.corolla N) cross

def term (M N : Signature K 4) (cross : Bool) (x : Fin 4 → Bool) (i j : Bool) : K :=
  M ![x 0,x 1,i,j] *
    N (if cross then ![x 2,x 3,!j,!i] else ![x 2,x 3,!i,!j])

/-- Both native edges are summed over, with their exact endpoint orientation. -/
theorem connect_denote (L R : Network K 4) (cross : Bool) (x : Fin 4 → Bool) :
    (connect L R cross).denote x =
      (term L.denote R.denote cross x false false + term L.denote R.denote cross x true false) +
      (term L.denote R.denote cross x false true + term L.denote R.denote cross x true true) := by
  rw [connect,Network.denote_contract,Network.denote_contract,
    Chain.reindex_denote,Chain.tensor_denote]
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply]
  cases cross
  all_goals
    dsimp [term,order]
    congr 4 <;> funext i <;> fin_cases i <;> rfl

theorem denote (M N : Signature K 4) (cross : Bool) (x : Fin 4 → Bool) :
    (network M N cross).denote x =
      (term M N cross x false false + term M N cross x true false) +
      (term M N cross x false true + term M N cross x true true) := by
  rw [network,connect_denote,Network.denote_corolla,Network.denote_corolla]

/-- The incidence may select any original ports. Reindexing applies to each
corolla's boundary, while both vertex labels retain their original ordering. -/
def onPorts (M N : Signature K 4) (e f : Equiv.Perm (Fin 4)) (cross : Bool) : Network K 4 :=
  connect (Chain.reindex (Network.corolla M) e) (Chain.reindex (Network.corolla N) f) cross

theorem onPorts_denote (M N : Signature K 4) (e f : Equiv.Perm (Fin 4)) (cross : Bool) :
    (onPorts M N e f cross).denote =
      (network (Tensor.reindex e M) (Tensor.reindex f N) cross).denote := by
  funext x
  rw [onPorts,connect_denote,Chain.reindex_denote,Chain.reindex_denote,
    Network.denote_corolla,Network.denote_corolla,denote]

theorem onPorts_realizes (M N : Signature K 4) (e f : Equiv.Perm (Fin 4)) (cross : Bool)
    (F : SignatureFamily K)
    (hM : (⟨4,M⟩ : AnySignature K) ∈ F) (hN : (⟨4,N⟩ : AnySignature K) ∈ F) :
    Gadget.Realizes F .disequality (onPorts M N e f cross).denote := by
  apply Gadget.realizes_network
  · intro v
    change Fin 2 at v
    fin_cases v
    · exact hM
    · exact hN
  · intro edge
    change Fin 2 at edge
    fin_cases edge <;> rfl

def labels (M N : Signature K 4) (cross : Bool) :
    Labelling (network M N cross).shape 2 1 (fun _ => 4) where
  vertex v := v
  vertex_arity v := by
    change 4 = (Network.tensorFinite (Network.corolla M) (Network.corolla N)).arity
      (finSumFinEquiv.symm v)
    cases finSumFinEquiv.symm v <;> rfl
  edge _ := 0

abbrev template (M N : Signature K 4) (cross : Bool) := (labels M N cross).template

theorem valid (M N : Signature K 4) (cross : Bool) :
    (template M N cross).WellFormed 2 1 (fun _ => 4) := (labels M N cross).wellFormed

theorem counts (M N : Signature K 4) (cross : Bool) :
    (template M N cross).boundary = 4 ∧ (template M N cross).vertices.length = 2 ∧
      (template M N cross).edges.length = 2 := by
  exact ⟨rfl,(labels M N cross).vertices_length,(labels M N cross).edges_length⟩

/-- The two original port lists and the two native edge labels are explicit. -/
theorem records (M N : Signature K 4) (cross : Bool) :
    (template M N cross).vertices =
      [(0,[.inl 0,.inl 1,.inr (1,false),.inr (0,false)]),
       (1,[.inl 2,.inl 3,
         if cross then .inr (0,true) else .inr (1,true),
         if cross then .inr (1,true) else .inr (0,true)])] ∧
      (template M N cross).edges = [0,0] := by
  cases cross <;> exact ⟨rfl,rfl⟩

theorem template_actual (M N : Signature K 4) (cross : Bool) :
    ((template M N cross).network (valid M N cross) ![M,N]
      (fun _ : Fin 1 => Signature.disequality)).denote = (network M N cross).denote := by
  apply Labelling.denote_template_of_labels (labels M N cross) _ _
    (network M N cross).vertex (network M N cross).edge
  · intro v t
    change Fin 2 at v
    fin_cases v <;> rfl
  · intro e a b
    change Fin 2 at e
    fin_cases e <;> rfl

theorem realizes (M N : Signature K 4) (cross : Bool) (F : SignatureFamily K)
    (hM : (⟨4,M⟩ : AnySignature K) ∈ F) (hN : (⟨4,N⟩ : AnySignature K) ∈ F) :
    Gadget.Realizes F .disequality (network M N cross).denote := by
  apply Gadget.realizes_network
  · intro v
    change Fin 2 at v
    fin_cases v
    · exact hM
    · exact hN
  · intro e
    change Fin 2 at e
    fin_cases e <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork
end
