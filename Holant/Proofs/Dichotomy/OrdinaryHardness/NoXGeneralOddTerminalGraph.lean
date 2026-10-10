import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralExposeEdgeValue

/-! Replace finitely many marked one-port vertices by actual Eq4 terminals.
Each terminal retains its old edge attachment, exposes one ordered boundary,
and closes its other two ports with an ordinary loop. No marked unary label
survives in the resulting original-family graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddTerminalGraph
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open OrdinaryNegativeCubicGadgets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K V E : Type} [Field K] [Fintype V] [Fintype E] {n s : ℕ} {a : ℕ→ℕ}
variable (N : FiniteNetwork K (V ⊕ Fin n) E 0) (unary : ∀j,N.arity (.inr j)=1)
abbrev RemainingPorts := Σv : V,Fin (N.arity (.inl v))

def oldPorts : (RemainingPorts N ⊕ Fin n) ≃ (Σv : V ⊕ Fin n,Fin (N.arity v)) where
  toFun
    | .inl p=>⟨.inl p.1,p.2⟩
    | .inr j=>⟨.inr j,Fin.cast (unary j).symm 0⟩
  invFun
    | ⟨.inl v,i⟩=>.inl ⟨v,i⟩
    | ⟨.inr j,_⟩=>.inr j
  left_inv p:=by cases p <;> rfl
  right_inv p:=by
    rcases p with ⟨v,i⟩
    cases v with
    | inl v=>rfl
    | inr j=>
        change (⟨Sum.inr j,Fin.cast (unary j).symm 0⟩ : Σv : V ⊕ Fin n,Fin (N.arity v))=⟨Sum.inr j,i⟩
        apply congrArg (fun k : Fin (N.arity (.inr j))=>(⟨Sum.inr j,k⟩ : Σv : V ⊕ Fin n,Fin (N.arity v)))
        apply Fin.ext
        have hi : i.val<1 := lt_of_lt_of_le i.isLt (le_of_eq (unary j))
        simp only [Fin.val_cast,Fin.val_zero]
        omega

def noBoundary : (Fin 0 ⊕ (E×Bool)) ≃ (E×Bool) where
  toFun:=Sum.elim Fin.elim0 id
  invFun:=Sum.inr
  left_inv p:=by cases p with | inl j=>exact Fin.elim0 j | inr p=>rfl
  right_inv _:=rfl

def oldEnds : (RemainingPorts N ⊕ Fin n) ≃ (E×Bool) :=
  (oldPorts N unary).trans (N.ports.trans noBoundary)

def terminalPorts (A : Type) (n : ℕ) : (A ⊕ (Fin n×Fin 4)) ≃ (Fin n ⊕ ((A ⊕ Fin n) ⊕ (Fin n×Bool))) where
  toFun
    | .inl p=>.inr (.inl (.inl p))
    | .inr (j,i)=>if i.val=0 then .inr (.inl (.inr j)) else
      if i.val=1 then .inl j else .inr (.inr (j,decide (i.val=3)))
  invFun
    | .inl j=>.inr (j,1)
    | .inr (.inl (.inl p))=>.inl p
    | .inr (.inl (.inr j))=>.inr (j,0)
    | .inr (.inr (j,false))=>.inr (j,2)
    | .inr (.inr (j,true))=>.inr (j,3)
  left_inv p:=by
    cases p with
    | inl _=>rfl
    | inr p=>rcases p with ⟨j,i⟩;fin_cases i <;> rfl
  right_inv p:=by
    rcases p with j|((p|j)|⟨j,b⟩)
    · rfl
    · rfl
    · rfl
    · cases b <;> rfl

def joinEnds : ((E×Bool) ⊕ (Fin n×Bool)) ≃ ((E ⊕ Fin n)×Bool) where
  toFun:=Sum.elim (fun p=>(.inl p.1,p.2)) (fun p=>(.inr p.1,p.2))
  invFun p:=match p.1 with | .inl e=>.inl (e,p.2) | .inr j=>.inr (j,p.2)
  left_inv p:=by cases p <;> rfl
  right_inv p:=by rcases p with ⟨e,b⟩;cases e <;> rfl

def arity : V ⊕ Fin n→ℕ := Sum.elim (fun v=>N.arity (.inl v)) (fun _=>4)

def newSigma : (Σ_ : Fin n,Fin 4) ≃ (Fin n×Fin 4) where
  toFun p:=(p.1,p.2)
  invFun p:=⟨p.1,p.2⟩
  left_inv _:=rfl
  right_inv _:=rfl

def ports : (Σv : V ⊕ Fin n,Fin (arity N v)) ≃ (Fin n ⊕ ((E ⊕ Fin n)×Bool)) :=
  (Equiv.sumSigmaDistrib (fun v=>Fin (arity N v))).trans
    ((Equiv.sumCongr (Equiv.refl _) newSigma).trans
      ((terminalPorts (RemainingPorts N) n).trans
        (Equiv.sumCongr (Equiv.refl _)
          ((Equiv.sumCongr (oldEnds N unary) (Equiv.refl _)).trans joinEnds))))

def finite : FiniteNetwork K (V ⊕ Fin n) (E ⊕ Fin n) n where
  arity:=arity N
  ports:=ports N unary
  vertex v:=match v with
    | .inl v=>N.vertex (.inl v)
    | .inr _=>Holant.EightVertex.ProductAnchor.equalityFour
  edge _:=Signature.equality

variable (H : (i : Fin s)→Signature K (a i.val)) (labels : V→Fin s)
variable (literal : ∀v,(⟨a (labels v).val,H (labels v)⟩ : AnySignature K)=⟨N.arity (.inl v),N.vertex (.inl v)⟩)
variable (eqLabel : Fin s)
variable (eqLiteral : (⟨a eqLabel.val,H eqLabel⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

def labelling : Labelling (finite N unary).toNetwork.shape s 1 a where
  vertex v:=Sum.elim labels (fun _=>eqLabel) ((Fintype.equivFin (V ⊕ Fin n)).symm v)
  vertex_arity v:=by
    change a (Sum.elim labels (fun _=>eqLabel) ((Fintype.equivFin (V ⊕ Fin n)).symm v)).val=
      arity N ((Fintype.equivFin (V ⊕ Fin n)).symm v)
    cases (Fintype.equivFin (V ⊕ Fin n)).symm v with
    | inl w=>exact congrArg Sigma.fst (literal w)
    | inr _=>exact congrArg Sigma.fst eqLiteral
  edge _:=0

def graph : Macro H n where
  network:=(finite N unary).toNetwork
  labels:=labelling N unary H labels literal eqLabel eqLiteral
  exact:=by
    have each (q : V ⊕ Fin n) :
        (⟨a (Sum.elim labels (fun _=>eqLabel) q).val,H (Sum.elim labels (fun _=>eqLabel) q)⟩ : AnySignature K)=
        ⟨arity N q,(finite N unary).vertex q⟩ := by
      cases q with
      | inl v=>exact literal v
      | inr _=>exact eqLiteral
    intro v
    exact each ((Fintype.equivFin (V ⊕ Fin n)).symm v)
  edges _:=rfl

omit [Field K] [Fintype V] [Fintype E] in
theorem old_route (v : V) (i : Fin (N.arity (.inl v))) :
    ports N unary ⟨.inl v,i⟩=.inr (.inl ((oldEnds N unary) (.inl ⟨v,i⟩)).1,
      ((oldEnds N unary) (.inl ⟨v,i⟩)).2) := rfl

omit [Field K] [Fintype V] [Fintype E] in
theorem new_route (j : Fin n) (i : Fin 4) : ports N unary ⟨.inr j,i⟩=
    ![.inr (.inl ((oldEnds N unary) (.inr j)).1,((oldEnds N unary) (.inr j)).2),
      .inl j,.inr (.inr j,false),.inr (.inr j,true)] i := by
  fin_cases i <;> rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddTerminalGraph
end
