import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddTerminalGraph

/-! The new Eq4 terminals condition the old marked variable bits. Their
ordinary loops each have exactly one supported assignment; the removed
one-port values do not occur in the resulting tensor. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddTerminalValue
open Holant Holant.Complexity
open OrdinaryNegativeCubicGadgets
open scoped BigOperators
namespace T
export NoXGeneralOddTerminalGraph (RemainingPorts arity oldEnds ports finite graph old_route new_route)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K V E : Type} [Field K] [Fintype V] [Fintype E] [DecidableEq E] {n s : ℕ} {a : ℕ→ℕ}
variable (N : FiniteNetwork K (V ⊕ Fin n) E 0) (unary : ∀j,N.arity (.inr j)=1)

def words : ((E ⊕ Fin n)→Bool) ≃ ((E→Bool)×(Fin n→Bool)) where
  toFun c:=(fun e=>c (.inl e),fun j=>c (.inr j))
  invFun p:=Sum.elim p.1 p.2
  left_inv c:=by funext e;cases e <;> rfl
  right_inv _:=rfl

def remainingWeight (c : E→Bool) : K :=
  ∏v,N.vertex (.inl v) (fun i=>c ((T.oldEnds N unary) (.inl ⟨v,i⟩)).1)

def rootBits (c : E→Bool) : Fin n→Bool := fun j=>c ((T.oldEnds N unary) (.inr j)).1

theorem equality_value (a b c : Bool) :
    Holant.EightVertex.ProductAnchor.equalityFour (K:=K) ![a,b,c,c]=
      if a=b ∧ c=b then 1 else 0 := by
  cases a <;> cases b <;> cases c <;>
    simp [Holant.EightVertex.ProductAnchor.equalityFour,Fin.forall_fin_succ]

omit [Fintype E] [DecidableEq E] in
theorem vertex_product (c : E→Bool) (l x : Fin n→Bool) :
    (∏v : V ⊕ Fin n,(T.finite N unary).vertex v
      (fun i=>Sum.elim x (fun p=>Sum.elim c l p.1) ((T.finite N unary).ports ⟨v,i⟩)))=
      remainingWeight N unary c*(if rootBits N unary c=x ∧ l=x then 1 else 0) := by
  rw [Fintype.prod_sum_type]
  have first : (∏v : V,(T.finite N unary).vertex (.inl v)
      (fun i=>Sum.elim x (fun p=>Sum.elim c l p.1) ((T.finite N unary).ports ⟨.inl v,i⟩)))=
      remainingWeight N unary c := by
    rfl
  rw [first]
  congr 1
  have term (j : Fin n) : (T.finite N unary).vertex (.inr j)
      (fun i=>Sum.elim x (fun p=>Sum.elim c l p.1) ((T.finite N unary).ports ⟨.inr j,i⟩))=
      if rootBits N unary c j=x j ∧ l j=x j then (1 : K) else 0 := by
    have hv : (fun i : Fin 4=>Sum.elim x (fun p=>Sum.elim c l p.1) (T.ports N unary ⟨.inr j,i⟩))=
        ![rootBits N unary c j,x j,l j,l j] := by
      funext i
      erw [T.new_route]
      fin_cases i <;> rfl
    change Holant.EightVertex.ProductAnchor.equalityFour _=_
    erw [hv,equality_value]
  simp_rw [term]
  simp only [Fintype.prod_boole,forall_and,←funext_iff]

variable (H : (i : Fin s)→Signature K (a i.val)) (labels : V→Fin s)
variable (literal : ∀v,(⟨a (labels v).val,H (labels v)⟩ : AnySignature K)=⟨N.arity (.inl v),N.vertex (.inl v)⟩)
variable (eqLabel : Fin s)
variable (eqLiteral : (⟨a eqLabel.val,H eqLabel⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

theorem value (x : Fin n→Bool) : (T.graph N unary H labels literal eqLabel eqLiteral).network.denote x=
    ∑c : E→Bool,if rootBits N unary c=x then remainingWeight N unary c else 0 := by
  classical
  rw [T.graph,FiniteNetwork.denote_toNetwork,NoXGeneralExposeEdgeValue.ordinary _ (fun _=>rfl)]
  rw [←Equiv.sum_comp (words (E:=E) (n:=n)).symm,Fintype.sum_prod_type]
  simp only [words,Equiv.coe_fn_symm_mk]
  simp_rw [vertex_product]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : rootBits N unary c=x <;> simp [h]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddTerminalValue
end
