import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets
import Holant.NetworkGluing.Finite
import Holant.Proofs.Tetrahedral.EvenCSPReduction.EqualityTree

/-! Replace one ordinary edge of a closed labelled graph by an Eq4 vertex
with two ordered exposed ports. The old two ends attach to its other ports;
every original vertex, edge orientation and coefficient is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralExposeEdgeGraph
open Holant Holant.Complexity Holant.Tractable Holant.Complexity.FixedGadgetSubstitution
open OrdinaryNegativeCubicGadgets
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (N : Macro H 0)
variable (eqLabel : Fin s)
variable (eqLiteral : (⟨a eqLabel.val,H eqLabel⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

abbrev Vertices := Fin N.network.shape.vertices ⊕ Unit
abbrev Edges := Fin N.network.shape.edges ⊕ Unit

def arity : Vertices H N→ℕ := Sum.elim N.network.shape.arity (fun _=>4)

def newPorts : (Σ_ : Unit,Fin 4) ≃ Fin 4 where
  toFun p:=p.2
  invFun i:=⟨(),i⟩
  left_inv p:=by rcases p with ⟨⟨⟩,i⟩;rfl
  right_inv _:=rfl

def basePorts : ((Fin N.network.shape.edges×Bool) ⊕ Fin 4) ≃ (Fin 2 ⊕ (Edges H N×Bool)) where
  toFun
    | .inl p=>.inr (.inl p.1,p.2)
    | .inr j=>if h : j.val<2 then .inl ⟨j.val,h⟩ else .inr (.inr (),decide (j.val=3))
  invFun
    | .inl j=>.inr ⟨j.val,by omega⟩
    | .inr (.inl e,b)=>.inl (e,b)
    | .inr (.inr _,false)=>.inr 2
    | .inr (.inr _,true)=>.inr 3
  left_inv p:=by
    cases p with
    | inl p=>rfl
    | inr j=>fin_cases j <;> rfl
  right_inv p:=by
    rcases p with j|⟨e,b⟩
    · fin_cases j <;> rfl
    · cases e with
      | inl e=>rfl
      | inr u=>cases u;cases b <;> rfl

variable (edge : Fin N.network.shape.edges)

def ports : (Σv : Vertices H N,Fin (arity H N v)) ≃ (Fin 2 ⊕ (Edges H N×Bool)) :=
  (Equiv.sumSigmaDistrib (fun v=>Fin (arity H N v))).trans
    ((Equiv.sumCongr (ClosedLabelling.closedPortEquiv N.network.shape) newPorts).trans
      ((basePorts H N).trans (Equiv.swap (.inr (.inl edge,true)) (.inr (.inr (),false)))))

def finite : FiniteNetwork K (Vertices H N) (Edges H N) 2 where
  arity:=arity H N
  ports:=ports H N edge
  vertex v:=match v with
    | .inl v=>N.network.vertex v
    | .inr _=>Holant.EightVertex.ProductAnchor.equalityFour
  edge _:=Signature.equality

def labels : Labelling (finite H N edge).toNetwork.shape s 1 a where
  vertex v:=Sum.elim N.labels.vertex (fun _=>eqLabel) ((Fintype.equivFin (Vertices H N)).symm v)
  vertex_arity v:=by
    change _=arity H N ((Fintype.equivFin (Vertices H N)).symm v)
    cases h : (Fintype.equivFin (Vertices H N)).symm v with
    | inl v=>exact N.labels.vertex_arity v
    | inr _=>exact congrArg Sigma.fst eqLiteral
  edge _:=0

def graph : Macro H 2 where
  network:=(finite H N edge).toNetwork
  labels:=labels H N eqLabel eqLiteral edge
  exact:=by
    have each (q : Vertices H N) :
        (⟨a (Sum.elim N.labels.vertex (fun _=>eqLabel) q).val,
          H (Sum.elim N.labels.vertex (fun _=>eqLabel) q)⟩ : AnySignature K)=
        ⟨arity H N q,(finite H N edge).vertex q⟩ := by
      cases q with
      | inl w=>exact N.exact w
      | inr _=>exact eqLiteral
    intro v
    exact each ((Fintype.equivFin (Vertices H N)).symm v)
  edges _:=rfl

theorem old_route (p : Σv : Fin N.network.shape.vertices,Fin (N.network.shape.arity v)) :
    ports H N edge ⟨.inl p.1,p.2⟩=
      if ClosedLabelling.closedPortEquiv N.network.shape p=(edge,true)
      then .inr (.inr (),false)
      else .inr (.inl (ClosedLabelling.closedPortEquiv N.network.shape p).1,
        (ClosedLabelling.closedPortEquiv N.network.shape p).2) := by
  change (Equiv.swap (α := Fin 2 ⊕ (Edges H N×Bool)) (.inr (.inl edge,true)) (.inr (.inr (),false)))
    (.inr (.inl (ClosedLabelling.closedPortEquiv N.network.shape p).1,
      (ClosedLabelling.closedPortEquiv N.network.shape p).2))=_
  generalize he : ClosedLabelling.closedPortEquiv N.network.shape p=db
  rcases db with ⟨d,b⟩
  cases b <;> by_cases hd : d=edge <;> simp [Equiv.swap_apply_def,hd]

theorem new_route (i : Fin 4) : ports H N edge ⟨.inr (),i⟩=
    ![.inl 0,.inl 1,.inr (.inl edge,true),.inr (.inr (),true)] i := by
  change (Equiv.swap (α := Fin 2 ⊕ (Edges H N×Bool)) (.inr (.inl edge,true)) (.inr (.inr (),false)))
    ((basePorts H N) (.inr i))=_
  fin_cases i <;> simp [basePorts,Equiv.swap_apply_def]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralExposeEdgeGraph
end
