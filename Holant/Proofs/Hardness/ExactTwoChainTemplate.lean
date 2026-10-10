import Holant.Proofs.Hardness.ExactTwoChain
import Holant.Complexity.BinaryInterpolation.Chains.Template

/-! Literal original-q labels on the actual four-port chains. The compiler
shape is independent of the coefficient field; its denotation still comes
from the same original q vertices and actual two-edge contractions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainTemplate
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export ExactTwoChain (q E B spectral series joinOrder network network_denote network_counts)
end C
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains
  (tensor reindex signature_cast_apply template_denote_heq)
end Chain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
variable {K : Type*} [Field K]

theorem signature (k : ℕ) (v : Fin (C.network (K:=K) k).shape.vertices) :
    (⟨(C.network (K:=K) k).shape.arity v,(C.network (K:=K) k).vertex v⟩ : AnySignature K)=⟨4,C.q⟩ := by
  induction k with
  | zero=>rfl
  | succ k ih=>
      change (⟨(Network.tensorFinite (C.network (K:=K) k) (Network.corolla C.q)).arity (finSumFinEquiv.symm v),
        (Network.tensorFinite (C.network (K:=K) k) (Network.corolla C.q)).vertex (finSumFinEquiv.symm v)⟩ : AnySignature K)=_
      cases finSumFinEquiv.symm v with
      | inl v=>exact ih v
      | inr v=>rfl

theorem arity (k : ℕ) (v : Fin (C.network (K:=K) k).shape.vertices) :
    (C.network (K:=K) k).shape.arity v=4 := congrArg Sigma.fst (signature k v)

theorem native (k : ℕ) : ∀e,(C.network (K:=K) k).edge e=Signature.disequality := by
  induction k with
  | zero=>intro e; exact Fin.elim0 e
  | succ k ih=>
      intro e
      refine Fin.cases rfl (fun e=>?_) e
      refine Fin.cases rfl (fun e=>?_) e
      change Sum.elim (C.network (K:=K) k).edge (Network.corolla C.q).edge
        (finSumFinEquiv.symm e)=Signature.disequality
      cases finSumFinEquiv.symm e with
      | inl e=>exact ih e
      | inr e=>exact Fin.elim0 e

theorem series_shape_independent {J : Type*} [Field J]
    (N M : Network K 4) (N' M' : Network J 4) (hN : N.shape=N'.shape) (hM : M.shape=M'.shape) :
    (C.series N M).shape=(C.series N' M').shape := by
  rcases N with ⟨SN,vN,eN⟩
  rcases M with ⟨SM,vM,eM⟩
  rcases N' with ⟨SN',vN',eN'⟩
  rcases M' with ⟨SM',vM',eM'⟩
  cases hN
  cases hM
  rfl

theorem shape_independent {J : Type*} [Field J] (k : ℕ) :
    (C.network (K:=K) k).shape=(C.network (K:=J) k).shape := by
  induction k with
  | zero=>rfl
  | succ k ih=>exact series_shape_independent _ _ _ _ ih rfl

def shapeTemplate (S : NetworkShape 4) (label edge : ℕ) : Template where
  boundary:=4
  vertices:=List.ofFn fun v : Fin S.vertices=>
    (label,List.ofFn fun i : Fin (S.arity v)=>Labelling.localEndpoint (S.ports ⟨v,i⟩))
  edges:=List.replicate S.edges edge

variable {s b : ℕ} (a : ℕ → ℕ) (label : Fin s) (hlabel : a label.val=4) (edge : Fin b)

def labels (k : ℕ) : Labelling (C.network (K:=K) k).shape s b a where
  vertex _:=label
  vertex_arity v:=hlabel.trans (arity k v).symm
  edge _:=edge

def literalTemplate (k : ℕ) : Template := (labels (K:=K) a label hlabel edge k).template

theorem literal_shape (k : ℕ) : literalTemplate (K:=K) a label hlabel edge k=
    shapeTemplate (C.network (K:=K) k).shape label.val edge.val := by
  simp [literalTemplate,shapeTemplate,Labelling.template,labels]

def compile (label edge k : ℕ) : Template := shapeTemplate (C.network (K:=ℚ) k).shape label edge

theorem compile_literal (k : ℕ) : compile label.val edge.val k=literalTemplate (K:=K) a label hlabel edge k := by
  rw [literal_shape,compile,shape_independent (K:=ℚ) (J:=K)]

include hlabel in
theorem valid (k : ℕ) : (compile label.val edge.val k).WellFormed s b a := by
  rw [compile_literal (K:=ℚ) a label hlabel edge k]
  exact (labels (K:=ℚ) a label hlabel edge k).wellFormed

theorem counts (label edge k : ℕ) :
    (compile label edge k).vertices.length=k+1 ∧ (compile label edge k).edges.length=2*k := by
  simpa only [compile,shapeTemplate,List.length_ofFn,List.length_replicate] using C.network_counts (K:=ℚ) k

theorem literal_denote (k : ℕ) (G : (i : Fin s) → Signature K (a i.val)) (X : Fin b → Kernel K)
    (hq : (⟨a label.val,G label⟩ : AnySignature K)=⟨4,C.q⟩) (hX : X edge=Signature.disequality) :
    ((literalTemplate (K:=K) a label hlabel edge k).network
      (labels (K:=K) a label hlabel edge k).wellFormed G X).denote=C.spectral ((2 : K)^k) := by
  rw [←C.network_denote k]
  apply Labelling.denote_template_of_labels
  · intro v x
    change G label (fun i=>x (Fin.cast (hlabel.trans (arity k v).symm) i))=(C.network (K:=K) k).vertex v x
    apply Chain.signature_cast_apply
    exact hq.trans (signature k v).symm
  · intro e x y
    exact congrFun₂ (hX.trans (native k e).symm) x y

theorem denote (k : ℕ) (G : (i : Fin s) → Signature K (a i.val)) (X : Fin b → Kernel K)
    (hq : (⟨a label.val,G label⟩ : AnySignature K)=⟨4,C.q⟩) (hX : X edge=Signature.disequality) :
    ((compile label.val edge.val k).network (valid a label hlabel edge k) G X).denote=C.spectral ((2 : K)^k) := by
  have he := Chain.template_denote_heq _ _ (valid a label hlabel edge k)
    (labels (K:=K) a label hlabel edge k).wellFormed (compile_literal (K:=K) a label hlabel edge k) G X
  exact (eq_of_heq he).trans (literal_denote a label hlabel edge k G X hq hX)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoChainTemplate
