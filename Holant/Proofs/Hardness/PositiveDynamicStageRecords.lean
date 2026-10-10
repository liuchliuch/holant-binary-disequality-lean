import Holant.Proofs.Hardness.PositiveDynamicStageTemplate

/-! Explicit literal rows for one positive dynamic block. Only the four outer
endpoint numbers change; labels and native internal edges remain original. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicStageRecords
open Holant Holant.Complexity FixedGadgetSubstitution
namespace D
export PositiveDynamicStage (swapAC rawStage stage blockChain)
end D
namespace T
export ExactTwoChainTemplate (shapeTemplate compile)
end T
namespace R
export ExactTwoChainRecords (explicitTemplate compile_eq)
end R
namespace DT
export PositiveDynamicStageTemplate (compile valid denote counts)
end DT
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (reindex)
end Chain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type*} [Field K]

def swapEndpoint : LocalEndpoint → LocalEndpoint
  | .inl i => .inl (if i=1 then 2 else if i=2 then 1 else i)
  | .inr p => .inr p

def swapRow (r : LocalVertex) : LocalVertex := (r.1,r.2.map swapEndpoint)

def swapTemplate (t : Template) : Template where
  boundary := t.boundary
  vertices := t.vertices.map swapRow
  edges := t.edges

theorem swap_localEndpoint {e : ℕ} (p : Fin 4 ⊕ (Fin e × Bool)) :
    (Template.embed 4 e ((Equiv.sumCongr D.swapAC (Equiv.refl _)) p) : LocalEndpoint)=
      swapEndpoint (Template.embed 4 e p) := by
  cases p with
  | inl i => fin_cases i <;> rfl
  | inr p => rfl

theorem shapeTemplate_reindex (N : Network K 4) (label edge : ℕ) :
    T.shapeTemplate (Chain.reindex N D.swapAC).shape label edge=
      swapTemplate (T.shapeTemplate N.shape label edge) := by
  unfold T.shapeTemplate swapTemplate Chain.reindex
  congr 1
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext v
  dsimp only [Function.comp_def,swapRow]
  rw [List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  exact swap_localEndpoint (N.shape.ports ⟨v,i⟩)

/-- Literal records obtained by swapping only boundary endpoints 1 and 2. -/
def singleBlock (label edge n : ℕ) : Template :=
  swapTemplate (R.explicitTemplate label edge (n-1))

theorem compile_singleBlock (label edge n : ℕ) :
    DT.compile label edge n 0=singleBlock label edge n := by
  unfold DT.compile D.blockChain D.stage
  rw [shapeTemplate_reindex]
  unfold D.rawStage
  rw [ThreeModeChain.shape_same]
  change swapTemplate (T.compile label edge (n-1))=_
  rw [R.compile_eq]
  rfl

theorem singleBlock_counts (label edge n : ℕ) (hn : 0<n) :
    (singleBlock label edge n).vertices.length=n ∧
      (singleBlock label edge n).edges.length=2*n-2 := by
  simpa only [compile_singleBlock,Nat.zero_add,Nat.mul_one] using DT.counts label edge n 0 hn

variable {s e : ℕ} (ar : ℕ → ℕ) (label : Fin s) (hlabel : ar label.val=4) (edge : Fin e)

include hlabel in
theorem singleBlock_valid (n : ℕ) : (singleBlock label.val edge.val n).WellFormed s e ar := by
  rw [←compile_singleBlock]
  exact DT.valid ar label hlabel edge n 0

theorem singleBlock_denote [CharZero K] (a b c : K) (n : ℕ) (hn : 0<n)
    (G : (i : Fin s) → Signature K (ar i.val)) (X : Fin e → Kernel K)
    (hq : (⟨ar label.val,G label⟩ : AnySignature K)=⟨4,ThreeModeSignatures.original a b c⟩)
    (hX : X edge=Signature.disequality) :
    ((singleBlock label.val edge.val n).network (singleBlock_valid ar label hlabel edge n) G X).denote=
      ThreeModeSignatures.spectral (PositiveDynamicStage.A a b n)
        (PositiveDynamicStage.B a b n+PositiveDynamicStage.C c n)
        (PositiveDynamicStage.B a b n-PositiveDynamicStage.C c n) := by
  have he := Holant.Complexity.BinaryInterpolation.Chains.template_denote_heq _ _
    (singleBlock_valid ar label hlabel edge n) (DT.valid ar label hlabel edge n 0)
    (compile_singleBlock label.val edge.val n).symm G X
  exact (eq_of_heq he).trans (by simpa using DT.denote ar label hlabel edge a b c n 0 hn G X hq hX)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicStageRecords
