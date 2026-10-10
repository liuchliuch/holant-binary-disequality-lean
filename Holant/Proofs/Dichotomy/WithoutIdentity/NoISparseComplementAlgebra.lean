import Holant.Proofs.Dichotomy.WithoutIdentity.NoIComplementFrame
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeComplementSign
import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeCoordinateLiteral

/-! Exact coefficient-field lift for a balanced complementary row. No
coefficient introduced by the common basis is identified with an old field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementAlgebra
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace S
export GlobalCloseCompletionComplementQ4Series (row)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K]

theorem form (q : Signature K 4) (even : EvenSupport q)
    (comp : PaperTerminalBridgeComplementSign.Complement q) :
    q=table ⟨(entries q).a,(entries q).b,(entries q).c,(entries q).d,
      (entries q).d,(entries q).c,(entries q).b,(entries q).x⟩ := by
  rw [←table_entries q even]
  congr 1
  apply Entries.ext <;> first | rfl | exact comp.1.symm | exact comp.2.1.symm | exact comp.2.2.symm

theorem mapped_form (phi : K→+*AlgebraicComplex) (q : Signature K 4) (even : EvenSupport q)
    (comp : PaperTerminalBridgeComplementSign.Complement q) :
    RingHomRealization.mapSignature phi q=table
      ⟨phi (entries q).a,phi (entries q).b,phi (entries q).c,phi (entries q).d,
        phi (entries q).d,phi (entries q).c,phi (entries q).b,phi (entries q).x⟩ := by
  have h:=form q even comp
  funext x
  change phi (q x)=_
  rw [congrFun h x]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [table,h0,h1,h2,h3]

theorem lift_row (phi : K→+*AlgebraicComplex) (f : AnySignature K)
    (a b c d : AlgebraicComplex)
    (literal : RingHomRealization.mapAny phi f=⟨4,S.row a b c d⟩) :
    ∃p q r s : K,phi p=a ∧ phi q=b ∧ phi r=c ∧ phi s=d ∧ f=⟨4,S.row p q r s⟩ := by
  obtain ⟨n,f⟩:=f
  have hn : n=4:=congrArg Sigma.fst literal
  subst n
  have hf : RingHomRealization.mapSignature phi f=S.row a b c d:=
    eq_of_heq (Sigma.mk.inj_iff.mp literal).2
  let e:=entries f
  have ha : phi e.a=a:=congrFun hf ![false,false,false,false]
  have hb : phi e.b=b:=congrFun hf ![false,false,true,true]
  have hc : phi e.c=c:=congrFun hf ![false,true,false,true]
  have hd : phi e.d=d:=congrFun hf ![false,true,true,false]
  refine ⟨e.a,e.b,e.c,e.d,ha,hb,hc,hd,?_⟩
  apply congrArg (fun q : Signature K 4=>(⟨4,q⟩ : AnySignature K))
  funext x
  apply phi.injective
  have h:=congrFun hf x
  change phi (f x)=_ at h
  rw [h]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [S.row,table,h0,h1,h2,h3,ha,hb,hc,hd]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoISparseComplementAlgebra
end
