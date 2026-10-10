import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryOrdinaryEquality

/-! The weighted ordinary Eq4 graph supplies its own diagonal binary by one
actual self-loop. A literal interpolated diagonal [1,a/b] corrects one leg,
giving scalar a times Eq4. Its occurrence is explicit, with no inverse-valued
original resource or uncharged normalization. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryDiagonalCorrection
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace W
export GlobalCloseCompletionUnaryOrdinaryEquality (endpoint)
end W
namespace C
export BinaryInterpolation.Chains (tensor tensor_denote reindex reindex_denote)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 8192
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ→ℕ}

def binary (N : Network K 4) : Network K 2 := N.contract Signature.equality

theorem binary_denote (N : Network K 4) (A B : K) (hN : N.denote=W.endpoint 4 A B) :
    (binary N).denote=W.endpoint 2 A B := by
  rw [binary,Network.denote_contract,hN]
  funext x
  rw [Signature.contract_equality]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [W.endpoint,purePin,funext_iff,Fin.forall_fin_succ,h0,h1]

def order : Equiv.Perm (Fin 6) where
  toFun := ![0,2,3,4,1,5]
  invFun := ![0,4,1,2,3,5]
  left_inv := by decide
  right_inv := by decide

def correct (N : Network K 4) (D : Network K 2) : Network K 4 :=
  (C.reindex (C.tensor N D) order).contract Signature.equality

theorem correct_value (N : Network K 4) (D : Network K 2) (x : Fin 4→Bool) :
    (correct N D).denote x=N.denote ![false,x 0,x 1,x 2]*D.denote ![false,x 3]+
      N.denote ![true,x 0,x 1,x 2]*D.denote ![true,x 3] := by
  rw [correct,Network.denote_contract,C.reindex_denote,C.tensor_denote,Signature.contract_equality]
  have eval (u v : Bool) :
      Tensor.reindex order (N.denote.tensor D.denote) (Fin.cons u (Fin.cons v x))=
        N.denote ![u,x 0,x 1,x 2]*D.denote ![v,x 3] := by
    simp only [Tensor.reindex_apply,Signature.tensor_apply]
    apply congrArg₂ (·*·)
    · apply congrArg N.denote; funext i; fin_cases i <;> rfl
    · apply congrArg D.denote; funext i; fin_cases i <;> rfl
  rw [eval,eval]

theorem correct_denote (N : Network K 4) (D : Network K 2) (A B U V : K)
    (hN : N.denote=W.endpoint 4 A B) (hD : D.denote=W.endpoint 2 U V) :
    (correct N D).denote=W.endpoint 4 (A*U) (B*V) := by
  funext x
  rw [correct_value,hN,hD]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [W.endpoint,purePin,funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

theorem corrected (N : Network K 4) (D : Network K 2) (A B : K) (hB : B≠0)
    (hN : N.denote=W.endpoint 4 A B) (hD : D.denote=W.endpoint 2 1 (A/B)) :
    (correct N D).denote=A • Holant.EightVertex.ProductAnchor.equalityFour := by
  have cancel : B*(A/B)=A := by field_simp
  rw [correct_denote N D A B 1 (A/B) hN hD,mul_one,cancel]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [W.endpoint,purePin,Holant.EightVertex.ProductAnchor.equalityFour,
      funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

def labels (N : Network K 4) (D : Network K 2)
    (NL : Labelling N.shape s 1 a) (DL : Labelling D.shape s 1 a) :
    Labelling (correct N D).shape s 1 a :=
  LabelledNetwork.contract _
    (LabelledNetwork.reindex _ (LabelledNetwork.tensor N D NL DL) order) 0 Signature.equality

theorem exact (F : (i : Fin s)→Signature K (a i.val)) (N : Network K 4) (D : Network K 2)
    (NL : Labelling N.shape s 1 a) (DL : Labelling D.shape s 1 a)
    (hN : LabelledNetwork.Exact F N NL) (hD : LabelledNetwork.Exact F D DL) :
    LabelledNetwork.Exact F (correct N D) (labels N D NL DL) :=
  LabelledNetwork.exact_tensor N D NL DL F hN hD

theorem ordinary (N : Network K 4) (D : Network K 2)
    (hN : ∀e,N.edge e=Signature.equality) (hD : ∀e,D.edge e=Signature.equality) :
    ∀e,(correct N D).edge e=Signature.equality := by
  intro e
  refine Fin.cases rfl (fun e=>?_) e
  change (Network.tensorFinite N D).edge (finSumFinEquiv.symm e)=_
  cases finSumFinEquiv.symm e with
  | inl e=>exact hN e
  | inr e=>exact hD e


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryDiagonalCorrection
end
