import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralExposeEdgeValue
import Holant.Proofs.Tetrahedral.EvenCSPReduction.Semantics

/-! Exposing the root edge of a genuine even-CSP variable cell gives its
conditioned partition, including all isolated variables and constant pins. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenDiagonalRoot
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open OrdinaryNegativeCubicGadgets
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open scoped BigOperators
namespace C
export Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Compilation
  (cell edgeIndex sourceNetwork labelling Words flatWords bits Supported supportedVariables supported_bits
   rowProduct rowProduct_guard vertex_product)
end C
namespace E
export NoXGeneralExposeEdgeGraph (graph)
export NoXGeneralExposeEdgeValue (oldWeight value)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (eqLabel : Fin s)
variable (eqLiteral : (⟨a eqLabel.val,H eqLabel⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (r : Raw.Input s a)

omit [Field K] in
private theorem literal_cast {m n : ℕ} (f : Signature K m) (h : m=n) :
    (⟨m,f⟩ : AnySignature K)=⟨n,fun x=>f (fun i=>x (Fin.cast h i))⟩ := by
  cases h
  rfl

def closed : Macro H 0 where
  network:=C.sourceNetwork r H eqLabel eqLiteral
  labels:={
    vertex:=(C.labelling r H eqLabel eqLiteral).vertex
    vertex_arity:=(C.labelling r H eqLabel eqLiteral).vertex_arity
    edge:=fun _=>0 }
  exact v:=literal_cast _ ((C.labelling r H eqLabel eqLiteral).vertex_arity v)
  edges _:=rfl

def rootEdge (i : Fin r.val.variables) : Fin (closed H eqLabel eqLiteral r).network.shape.edges :=
  C.edgeIndex r ⟨i,(C.cell r i).root⟩

def graph (i : Fin r.val.variables) : Macro H 2 :=
  E.graph H (closed H eqLabel eqLiteral r) eqLabel eqLiteral (rootEdge H eqLabel eqLiteral r i)

def conditional (i : Fin r.val.variables) (b : Bool) : K :=
  ∑x : Fin r.val.variables→Bool,if x i=b then Raw.factorWeight H r (fun p=>x (Raw.route r p)) else 0

theorem flat_root (w : C.Words r) (i : Fin r.val.variables) :
    C.flatWords r w (rootEdge H eqLabel eqLiteral r i)=w i (C.cell r i).root := by
  change (let q:=(C.edgeIndex r).symm (C.edgeIndex r ⟨i,(C.cell r i).root⟩);w q.1 q.2)=_
  rw [Equiv.symm_apply_apply]

theorem root_value (i : Fin r.val.variables) (b : Bool) :
    (∑c : Fin (closed H eqLabel eqLiteral r).network.shape.edges→Bool,
      if c (rootEdge H eqLabel eqLiteral r i)=b then E.oldWeight H (closed H eqLabel eqLiteral r) c else 0)=
      conditional H r i b := by
  classical
  have weights (w : C.Words r) : E.oldWeight H (closed H eqLabel eqLiteral r) (C.flatWords r w)=
      Raw.factorWeight H r (C.bits r w)*C.rowProduct (K:=K) r w :=
    C.vertex_product r H eqLabel eqLiteral w
  erw [←Equiv.sum_comp (C.flatWords r)]
  simp_rw [flat_root,weights,C.rowProduct_guard]
  rw [Finset.sum_congr_set {w : C.Words r | C.Supported r w}
    (fun w=>if w i (C.cell r i).root=b then
      Raw.factorWeight H r (C.bits r w)*(if C.Supported r w then 1 else 0) else 0)
    (fun w=>if w.val i (C.cell r i).root=b then Raw.factorWeight H r (C.bits r w.val) else 0)
    (by intro w hw;change C.Supported r w at hw;simp only [ite_eq_left hw,mul_one])
    (by intro w hw;change ¬C.Supported r w at hw;simp only [ite_eq_right hw,mul_zero,ite_self])]
  unfold conditional
  apply Fintype.sum_equiv (C.supportedVariables r)
  intro w
  change (if w.val i (C.cell r i).root=b then Raw.factorWeight H r (C.bits r w.val) else 0)=
    (if w.val i (C.cell r i).root=b then
      Raw.factorWeight H r (fun p=>w.val (Raw.route r p) (C.cell r (Raw.route r p)).root) else 0)
  congr 1
  congr 1
  funext p
  exact C.supported_bits r w.val w.property p

theorem value (i : Fin r.val.variables) (x : Fin 2→Bool) :
    (graph H eqLabel eqLiteral r i).network.denote x=
      if x 0=x 1 then conditional H r i (x 0) else 0 := by
  rw [graph,E.value,root_value]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenDiagonalRoot
end
