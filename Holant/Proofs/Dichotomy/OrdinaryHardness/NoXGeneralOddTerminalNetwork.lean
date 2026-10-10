import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddTerminalValue

/-! Reindex a concrete closed network into retained and marked occurrences,
then replace all marked temporary unary ones by actual Eq4 terminals. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddTerminalNetwork
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open OrdinaryNegativeCubicGadgets
open scoped BigOperators
namespace T
export NoXGeneralOddTerminalGraph (graph oldEnds)
export NoXGeneralOddTerminalValue (value remainingWeight rootBits)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K V : Type} [Field K] [Fintype V] {n s : ℕ} {a : ℕ→ℕ}
variable (N : Network K 0) (vertices : (V ⊕ Fin n) ≃ Fin N.shape.vertices)
variable (unary : ∀j,N.shape.arity (vertices (.inr j))=1)

def finite : FiniteNetwork K (V ⊕ Fin n) (Fin N.shape.edges) 0 where
  arity v:=N.shape.arity (vertices v)
  ports:=(Equiv.sigmaCongrLeft vertices).trans N.shape.ports
  vertex v:=N.vertex (vertices v)
  edge:=N.edge

variable (H : (i : Fin s)→Signature K (a i.val)) (labels : V→Fin s)
variable (literal : ∀v,(⟨a (labels v).val,H (labels v)⟩ : AnySignature K)=
  ⟨N.shape.arity (vertices (.inl v)),N.vertex (vertices (.inl v))⟩)
variable (eqLabel : Fin s)
variable (eqLiteral : (⟨a eqLabel.val,H eqLabel⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

def graph : Macro H n := T.graph (finite N vertices) unary H labels literal eqLabel eqLiteral

def markerEdge (j : Fin n) : Fin N.shape.edges :=
  (ClosedLabelling.closedPortEquiv N.shape ⟨vertices (.inr j),Fin.cast (unary j).symm 0⟩).1

def weight (c : Fin N.shape.edges→Bool) : K :=
  ∏v,N.vertex v (N.shape.assignment Fin.elim0 (fun p=>c p.1) v)

omit [Field K] [Fintype V] in
theorem roots (c : Fin N.shape.edges→Bool) :
    T.rootBits (finite N vertices) unary c=fun j=>c (markerEdge N vertices unary j) := rfl

omit [Field K] [Fintype V] in
theorem remaining_word (c : Fin N.shape.edges→Bool) (v : V) :
    (fun i=>c ((T.oldEnds (finite N vertices) unary) (.inl ⟨v,i⟩)).1)=
      N.shape.assignment Fin.elim0 (fun p=>c p.1) (vertices (.inl v)) := by
  funext i
  rw [ClosedLabelling.closed_assignment]
  rfl

variable (ones : ∀j,∀x : Fin (N.shape.arity (vertices (.inr j)))→Bool,
  N.vertex (vertices (.inr j)) x=1)

include ones in
theorem remaining_value (c : Fin N.shape.edges→Bool) :
    T.remainingWeight (finite N vertices) unary c=weight N c := by
  unfold T.remainingWeight weight
  simp_rw [remaining_word]
  rw [←Equiv.prod_comp vertices]
  simp only [Fintype.prod_sum_type,ones,Finset.prod_const_one,mul_one]
  rfl

include ones in
theorem value (x : Fin n→Bool) : (graph N vertices unary H labels literal eqLabel eqLiteral).network.denote x=
    ∑c : Fin N.shape.edges→Bool,(if (fun j=>c (markerEdge N vertices unary j))=x then weight N c else 0) := by
  rw [graph,T.value]
  simp_rw [roots,remaining_value N vertices unary ones]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddTerminalNetwork
end
