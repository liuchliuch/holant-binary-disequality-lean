import Holant.Proofs.Dichotomy.Closure.Sparse.GlobalCloseCompletionSparseEq4Flip

/-! A weighted native ternary equality gives an actual equality-four graph.
The weights cancel between two opposite copies; no root extraction,
interpolation, chart change, or extra signature is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryEndpointEq4
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export BinaryInterpolation.Chains (tensor tensor_denote reindex reindex_denote)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 8192
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ → ℕ}

/-- Both constant words may carry arbitrary nonzero, unequal weights. -/
def endpoint (A B : K) : Signature K 3 := fun x =>
  if x 0=x 1 ∧ x 1=x 2 then if x 0 then B else A else 0

def order : Equiv.Perm (Fin 6) where
  toFun := ![0,2,4,1,3,5]
  invFun := ![0,3,1,4,2,5]
  left_inv := by decide
  right_inv := by decide

def double (N : Network K 3) : Network K 4 :=
  (C.reindex (C.tensor N N) order).contract Signature.disequality

theorem double_value (N : Network K 3) (x : Fin 4 → Bool) :
    (double N).denote x =
      N.denote ![false,x 0,x 2]*N.denote ![true,x 1,x 3] +
      N.denote ![true,x 0,x 2]*N.denote ![false,x 1,x 3] := by
  rw [double,Network.denote_contract_disequality,C.reindex_denote,C.tensor_denote]
  have eval (u v : Bool) :
      Tensor.reindex order (N.denote.tensor N.denote) (Fin.cons u (Fin.cons v x)) =
        N.denote ![u,x 0,x 2]*N.denote ![v,x 1,x 3] := by
    simp only [Tensor.reindex_apply,Signature.tensor_apply]
    apply congrArg₂ (·*·)
    all_goals apply congrArg N.denote; funext i; fin_cases i <;> rfl
  rw [eval,eval]

theorem double_denote (N : Network K 3) (A B : K)
    (hN : N.denote=endpoint A B) :
    (double N).denote=(A*B) • ExactTwoSignatures.E := by
  funext x
  rw [double_value,hN]
  simp only [Pi.smul_apply,smul_eq_mul,ExactTwoSignatures.E_reference]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [endpoint,h0,h1,h2,h3,mul_comm]

def doubleLabels (N : Network K 3) (NL : Labelling N.shape s 1 a) :
    Labelling (double N).shape s 1 a :=
  LabelledNetwork.contract _
    (LabelledNetwork.reindex _ (LabelledNetwork.tensor N N NL NL) order)
    0 Signature.disequality

theorem double_exact (F : (i : Fin s) → Signature K (a i.val))
    (N : Network K 3) (NL : Labelling N.shape s 1 a)
    (hN : LabelledNetwork.Exact F N NL) :
    LabelledNetwork.Exact F (double N) (doubleLabels N NL) :=
  LabelledNetwork.exact_tensor N N NL NL F hN hN

theorem double_native (N : Network K 3)
    (hN : ∀e,N.edge e=Signature.disequality) :
    ∀e,(double N).edge e=Signature.disequality := by
  intro e
  refine Fin.cases rfl (fun e => ?_) e
  change (Network.tensorFinite N N).edge (finSumFinEquiv.symm e)=_
  cases finSumFinEquiv.symm e with
  | inl e => exact hN e
  | inr e => exact hN e

/-- A fully labelled, exact central four-port resource in the same palette. -/
def central (F : (i : Fin s) → Signature K (a i.val))
    (N : Network K 3) (NL : Labelling N.shape s 1 a)
    (hE : LabelledNetwork.Exact F N NL) (hX : ∀e,N.edge e=Signature.disequality)
    (A B : K) (hA : A≠0) (hB : B≠0) (hN : N.denote=endpoint A B) :
    GeneralEODEQProducerNormalize.Produced F :=
  ⟨double N,doubleLabels N NL,double_exact F N NL hE,double_native N hX,
    A*B,mul_ne_zero hA hB,double_denote N A B hN⟩

variable {r : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin r) → Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

/-- The real Eq4 source consumed by Eq4FullSource, with original field and
original labels. Retained literal identity supplies the two physical flips. -/
def produce (N : Network (OI.K G) 3) (NL : Labelling N.shape P.count 1 P.arity)
    (hE : LabelledNetwork.Exact P.table N NL) (hX : ∀e,N.edge e=Signature.disequality)
    (A B : OI.K G) (hA : A≠0) (hB : B≠0) (hN : N.denote=endpoint A B) :
    GlobalCloseCompletionEq4Graph.Output G P :=
  GlobalCloseCompletionSparseEq4Flip.produce G P (central P.table N NL hE hX A B hA hB hN)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryEndpointEq4
end
