import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput
import Holant.NetworkAlgebra

/-! One native-X edge joins the first port of an arbitrary actual row to
one Eq4 port. All remaining old ports precede the three new ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeAttach
open Holant Holant.Complexity
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}
abbrev Edges (L : Network K (n+1)) (R : Network K 4):=(Fin L.shape.edges⊕Fin R.shape.edges)⊕Unit

def ports (EL ER : Type) (n : ℕ) :
    ((Fin (n+1)⊕(EL×Bool))⊕(Fin 4⊕(ER×Bool)))≃(Fin (n+3)⊕((((EL⊕ER)⊕Unit)×Bool))) where
  toFun
    | .inl (.inl i)=>Fin.cases (.inr (.inr (),false)) (fun j=>.inl (Fin.castAdd 3 j)) i
    | .inr (.inl i)=>Fin.cases (.inr (.inr (),true)) (fun j=>.inl (Fin.natAdd n j)) i
    | .inl (.inr (e,b))=>.inr (.inl (.inl e),b)
    | .inr (.inr (e,b))=>.inr (.inl (.inr e),b)
  invFun
    | .inl i=>match (finSumFinEquiv : Fin n⊕Fin 3≃Fin (n+3)).symm i with
      | .inl j=>.inl (.inl j.succ)
      | .inr j=>.inr (.inl j.succ)
    | .inr (.inl (.inl e),b)=>.inl (.inr (e,b))
    | .inr (.inl (.inr e),b)=>.inr (.inr (e,b))
    | .inr (.inr (),false)=>.inl (.inl 0)
    | .inr (.inr (),true)=>.inr (.inl 0)
  left_inv:=by
    rintro ((i|⟨e,b⟩)|(i|⟨e,b⟩))
    · refine Fin.cases rfl (fun j=>?_) i
      simp only [Fin.cases_succ,finSumFinEquiv_symm_apply_castAdd]
    · rfl
    · refine Fin.cases rfl (fun j=>?_) i
      simp only [Fin.cases_succ,finSumFinEquiv_symm_apply_natAdd]
    · rfl
  right_inv:=by
    rintro (i|⟨((e|e)|u),b⟩)
    · obtain ⟨j,rfl⟩:=(finSumFinEquiv : Fin n⊕Fin 3≃Fin (n+3)).surjective i
      cases j <;> simp
    · rfl
    · rfl
    · cases u;cases b <;> rfl

def finite (L : Network K (n+1)) (R : Network K 4) :
    FiniteNetwork K (Fin L.shape.vertices⊕Fin R.shape.vertices) (Edges L R) (n+3) where
  arity:=Sum.elim L.shape.arity R.shape.arity
  ports:=(Equiv.sumSigmaDistrib (fun v=>Fin (Sum.elim L.shape.arity R.shape.arity v))).trans
    ((Equiv.sumCongr L.shape.ports R.shape.ports).trans (ports _ _ n))
  vertex
    | .inl v=>L.vertex v
    | .inr v=>R.vertex v
  edge
    | .inl (.inl e)=>L.edge e
    | .inl (.inr e)=>R.edge e
    | .inr _=>Signature.disequality

def assignments (L : Network K (n+1)) (R : Network K 4) :
    ((Edges L R×Bool)→Bool)≃(Bool×(Bool×(((Fin L.shape.edges×Bool)→Bool)×((Fin R.shape.edges×Bool)→Bool)))) where
  toFun z:=(z (.inr (),false),z (.inr (),true),fun p=>z (.inl (.inl p.1),p.2),fun p=>z (.inl (.inr p.1),p.2))
  invFun p
    | (.inr (),false)=>p.1
    | (.inr (),true)=>p.2.1
    | (.inl (.inl e),b)=>p.2.2.1 (e,b)
    | (.inl (.inr e),b)=>p.2.2.2 (e,b)
  left_inv z:=by funext p;rcases p with ⟨((e|e)|u),b⟩ <;> cases b <;> first | rfl | (cases u;rfl)
  right_inv p:=rfl

def leftWord (x : Fin (n+3)→Bool) : Fin n→Bool:=fun i=>x (Fin.castAdd 3 i)
def rightWord (x : Fin (n+3)→Bool) : Fin 3→Bool:=fun i=>x (Fin.natAdd n i)

theorem value (L : Network K (n+1)) (R : Network K 4) (x : Fin (n+3)→Bool) :
    (finite L R).denote x=∑a : Bool,∑b : Bool,
      L.denote (Fin.cons a (leftWord x))*R.denote (Fin.cons b (rightWord x))*Signature.disequality a b := by
  classical
  letI : DecidableEq (Edges L R):=Classical.decEq _
  unfold FiniteNetwork.denote
  erw [←(assignments L R).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Network.denote,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro zL _
  apply Finset.sum_congr rfl
  intro zR _
  simp only [finite,Fintype.prod_sum_type,Fintype.prod_unique]
  have hl : (fun (v : Fin L.shape.vertices) (i : Fin (L.shape.arity v))=>
      Sum.elim x ((assignments L R).symm (a,b,zL,zR)) ((finite L R).ports ⟨.inl v,i⟩))=
      L.shape.assignment (Fin.cons a (leftWord x)) zL := by
    funext v i
    change Sum.elim x _ (ports _ _ n (.inl (L.shape.ports ⟨v,i⟩)))=
      Sum.elim (Fin.cons a (leftWord x)) zL (L.shape.ports ⟨v,i⟩)
    cases hp : L.shape.ports ⟨v,i⟩ with
    | inr p=>rfl
    | inl j=>
      refine Fin.cases ?_ (fun j=>?_) j <;> rfl
  have hr : (fun (v : Fin R.shape.vertices) (i : Fin (R.shape.arity v))=>
      Sum.elim x ((assignments L R).symm (a,b,zL,zR)) ((finite L R).ports ⟨.inr v,i⟩))=
      R.shape.assignment (Fin.cons b (rightWord x)) zR := by
    funext v i
    change Sum.elim x _ (ports _ _ n (.inr (R.shape.ports ⟨v,i⟩)))=
      Sum.elim (Fin.cons b (rightWord x)) zR (R.shape.ports ⟨v,i⟩)
    cases hp : R.shape.ports ⟨v,i⟩ with
    | inr p=>rfl
    | inl j=>refine Fin.cases ?_ (fun j=>?_) j <;> rfl
  dsimp only [finite,assignments,Equiv.coe_fn_symm_mk] at hl hr ⊢
  simp only [congrFun₂ hl,congrFun₂ hr]
  ring

variable [Algebra ℚ K] {s : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val))
variable (L : NativeAntiTargetSource.Output H (n+1)) (R : NativeAntiTargetSource.Output H 4)
abbrev network:=(finite L.network R.network).toNetwork

def labels : FixedGadgetSubstitution.Labelling (network H L R).shape s 1 a where
  vertex v:=Sum.elim L.labels.vertex R.labels.vertex ((Fintype.equivFin _).symm v)
  vertex_arity v:=by
    change a (Sum.elim L.labels.vertex R.labels.vertex ((Fintype.equivFin _).symm v)).val=
      Sum.elim L.network.shape.arity R.network.shape.arity ((Fintype.equivFin _).symm v)
    cases (Fintype.equivFin (Fin L.network.shape.vertices⊕Fin R.network.shape.vertices)).symm v with
    | inl w=>exact L.labels.vertex_arity w
    | inr w=>exact R.labels.vertex_arity w
  edge _:=0

def output : NativeAntiTargetSource.Output H (n+3) where
  network:=network H L R
  labels:=labels H L R
  exact v:=by
    change _=(⟨_,(finite L.network R.network).vertex ((Fintype.equivFin _).symm v)⟩ : AnySignature K)
    dsimp only [labels]
    cases (Fintype.equivFin (Fin L.network.shape.vertices⊕Fin R.network.shape.vertices)).symm v with
    | inl w=>exact L.exact w
    | inr w=>exact R.exact w
  native e:=by
    change (finite L.network R.network).edge ((Fintype.equivFin _).symm e)=_
    cases (Fintype.equivFin (Edges L.network R.network)).symm e with
    | inr _=>rfl
    | inl w=>cases w with
      | inl e=>exact L.native e
      | inr e=>exact R.native e

theorem output_value (x : Fin (n+3)→Bool) :
    (output H L R).network.denote x=∑a : Bool,∑b : Bool,
      L.network.denote (Fin.cons a (leftWord x))*R.network.denote (Fin.cons b (rightWord x))*Signature.disequality a b := by
  rw [show (output H L R).network=(finite L.network R.network).toNetwork from rfl,FiniteNetwork.denote_toNetwork]
  exact value L.network R.network x

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureMergeAttach
end
