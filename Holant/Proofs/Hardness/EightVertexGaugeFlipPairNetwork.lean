import Holant.Proofs.Hardness.EightVertexGaugeTwoRowNetwork

/-! Flip precisely original ports 2 and 3 by two literal retained I vertices.
The graph has one original four-port row, two ordered I labels and two native
X edges. Ports 0 and 1 are untouched; no free boundary bit-flip is inserted. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeFlipPairNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex tensor_denote reindex_denote)
end Chain
variable {K : Type} [Field K]

def identity : Signature K 2 := fun x => Signature.equality (x 0) (x 1)

/-- Original [I00,I01,I10,I11] becomes [I00,I10,I01,I11]. -/
def identityPair : Network K 4 :=
  Chain.reindex (Chain.tensor (Network.corolla identity) (Network.corolla identity))
    (Equiv.swap (1 : Fin 4) 2)

theorem identityPair_denote : (identityPair (K := K)).denote = fun x =>
    Signature.equality (x 0) (x 2) * Signature.equality (x 1) (x 3) := by
  rw [identityPair,Chain.reindex_denote,Chain.tensor_denote,
    Network.denote_corolla]
  funext x
  simp [Tensor.reindex_apply,Signature.tensor_apply,identity,Equiv.swap_apply_def]

def network (M : Signature K 4) : Network K 4 :=
  EightVertexGaugeTwoRowNetwork.connect (Network.corolla M) identityPair false

def value (M : Signature K 4) : Signature K 4 := fun x => M ![x 0,x 1,!(x 2),!(x 3)]

theorem denote (M : Signature K 4) : (network M).denote = value M := by
  funext x
  rw [network,EightVertexGaugeTwoRowNetwork.connect_denote,
    Network.denote_corolla,identityPair_denote]
  cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [EightVertexGaugeTwoRowNetwork.term,value,Signature.equality,h2,h3]

def arity (i : ℕ) : ℕ := if i = 0 then 4 else 2

def labels (M : Signature K 4) : Labelling (network M).shape 2 1 arity where
  vertex v := if v.val = 0 then 0 else 1
  vertex_arity v := by
    change Fin 3 at v
    fin_cases v <;> rfl
  edge _ := 0

abbrev template (M : Signature K 4) := (labels M).template

theorem valid (M : Signature K 4) : (template M).WellFormed 2 1 arity :=
  (labels M).wellFormed

theorem records (M : Signature K 4) :
    (template M).boundary = 4 ∧ (template M).vertices =
      [(0,[.inl 0,.inl 1,.inr (1,false),.inr (0,false)]),
       (1,[.inl 2,.inr (1,true)]),(1,[.inl 3,.inr (0,true)])] ∧
      (template M).edges = [0,0] := by
  exact ⟨rfl,rfl,rfl⟩

theorem counts (M : Signature K 4) :
    (network M).shape.vertices = 3 ∧ (network M).shape.edges = 2 := ⟨rfl,rfl⟩

theorem native (M : Signature K 4) : ∀ e, (network M).edge e = Signature.disequality := by
  intro e
  change Fin 2 at e
  fin_cases e <;> rfl

theorem realizes (M : Signature K 4) (F : SignatureFamily K)
    (hM : (⟨4,M⟩ : AnySignature K) ∈ F)
    (hI : (⟨2,identity⟩ : AnySignature K) ∈ F) :
    Gadget.Realizes F .disequality (value M) := by
  rw [← denote]
  apply Gadget.realizes_network
  · intro v
    change Fin 3 at v
    fin_cases v
    · exact hM
    · exact hI
    · exact hI
  · exact native M

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeFlipPairNetwork
end
