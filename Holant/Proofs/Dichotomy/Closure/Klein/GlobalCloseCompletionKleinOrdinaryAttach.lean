import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryPair
import Holant.Certificates.EqualityQuaternary.KleinOrbitProgram

/-! Actual ordinary-I attachment of an arbitrary retained binary row at any
original port. The binary's port zero is exposed and port one is joined; no
analytic port action is declared to be a free resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryAttach
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Certificates.EqualityQuaternary
namespace C
export BinaryInterpolation.Chains (tensor tensor_denote reindex reindex_denote)
end C
namespace O
export Klein.Orbit (site)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

def binary (B : Kernel K) : Signature K 2 := fun x=>B (x 0) (x 1)

def middle (N : Network K 4) (B : Kernel K) : Network K 4 :=
  (C.reindex (C.tensor N (Network.corolla (binary B)))
    (GlobalCloseCompletionSparseEq4Flip.order false)).contract Signature.equality

theorem middle_denote (N : Network K 4) (B : Kernel K) :
    (middle N B).denote=O.site B 1 N.denote := by
  funext x
  rw [middle,Network.denote_contract_equality,C.reindex_denote,C.tensor_denote,Network.denote_corolla]
  have eval (u v : Bool) :
      Tensor.reindex (GlobalCloseCompletionSparseEq4Flip.order false)
        (N.denote.tensor (binary B)) (Fin.cons u (Fin.cons v x))=
      N.denote (Function.update x 1 u)*B (x 1) v := by
    simp only [Tensor.reindex_apply,Signature.tensor_apply]
    have left : (fun i : Fin 4=>(Fin.cons u (Fin.cons v x) : Fin 6→Bool)
        ((GlobalCloseCompletionSparseEq4Flip.order false) (Fin.castAdd 2 i)))=Function.update x 1 u := by
      funext i
      fin_cases i <;> simp [GlobalCloseCompletionSparseEq4Flip.order,Function.update] <;> rfl
    have right : (fun i : Fin 2=>(Fin.cons u (Fin.cons v x) : Fin 6→Bool)
        ((GlobalCloseCompletionSparseEq4Flip.order false) (Fin.natAdd 4 i)))=![x 1,v] := by
      funext i
      fin_cases i <;> rfl
    rw [left,right]
    rfl
  rw [eval,eval]
  simp [O.site,Fintype.sum_bool,mul_comm,add_comm]

def attach (N : Network K 4) (i : Fin 4) (B : Kernel K) : Network K 4 :=
  C.reindex (middle (C.reindex N (Equiv.swap 1 i)) B) (Equiv.swap 1 i)

theorem attach_denote (N : Network K 4) (i : Fin 4) (B : Kernel K) :
    (attach N i B).denote=O.site B i N.denote := by
  rw [attach,C.reindex_denote,middle_denote,C.reindex_denote]
  funext x
  simp only [Tensor.reindex_apply,O.site,Equiv.swap_apply_right]
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  funext j
  by_cases hj : j=i
  · subst j
    simp [Function.update]
  · have different : (Equiv.swap (1 : Fin 4) i) j≠1 := by
      intro he
      apply hj
      have h := congrArg (Equiv.swap (1 : Fin 4) i) he
      simpa using h
    simp [Function.update,different,hj]

section Labels
variable {s : ℕ} {a : ℕ→ℕ} (H : (i : Fin s)→Signature K (a i.val))
variable (N : Network K 4) (L : Labelling N.shape s 1 a) (j : Fin s) (B : Kernel K)
variable (literal : (⟨a j.val,H j⟩ : AnySignature K)=⟨2,binary B⟩)

def binaryLabels : Labelling (Network.corolla (binary B)).shape s 1 a where
  vertex _ := j
  vertex_arity _ := congrArg Sigma.fst literal
  edge := Fin.elim0

def middleLabels : Labelling (middle N B).shape s 1 a :=
  LabelledNetwork.contract _ (LabelledNetwork.reindex _
    (LabelledNetwork.tensor _ _ L (binaryLabels H j B literal))
    (GlobalCloseCompletionSparseEq4Flip.order false)) 0 Signature.equality

def labels (i : Fin 4) : Labelling (attach N i B).shape s 1 a :=
  LabelledNetwork.reindex _
    (middleLabels H (C.reindex N (Equiv.swap 1 i))
      (LabelledNetwork.reindex N L (Equiv.swap 1 i)) j B literal) (Equiv.swap 1 i)

theorem exact (i : Fin 4) (input : LabelledNetwork.Exact H N L) :
    LabelledNetwork.Exact H (attach N i B) (labels H N L j B literal i) :=
  LabelledNetwork.exact_tensor (C.reindex N (Equiv.swap 1 i)) (Network.corolla (binary B))
    (LabelledNetwork.reindex N L (Equiv.swap 1 i)) (binaryLabels H j B literal) H input (fun _=>literal)
end Labels

theorem ordinary (N : Network K 4) (i : Fin 4) (B : Kernel K)
    (input : ∀e,N.edge e=Signature.equality) :
    ∀e,(attach N i B).edge e=Signature.equality := by
  intro e
  refine Fin.cases rfl (fun e=>?_) e
  change (Network.tensorFinite (C.reindex N (Equiv.swap 1 i)) (Network.corolla (binary B))).edge
    (finSumFinEquiv.symm e)=_
  cases finSumFinEquiv.symm e with
  | inl e => exact input e
  | inr e => exact Fin.elim0 e


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryAttach
end
