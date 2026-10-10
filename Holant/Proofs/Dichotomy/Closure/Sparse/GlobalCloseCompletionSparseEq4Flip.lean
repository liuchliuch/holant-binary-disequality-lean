import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Graph
import Holant.Proofs.Hardness.GeneralEODEQProducerNormalize

/-! Two physical literal-I legs turn central DEQ4 into equality-four. The
original labels, field and native-X edges are retained throughout. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseEq4Flip
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export BinaryInterpolation.Chains (tensor tensor_denote reindex reindex_denote binarySignature)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {K : Type*} [Field K] {s : ℕ} {a : ℕ → ℕ}

def identity : Signature K 2 := fun x => Signature.equality (x 0) (x 1)

def order (b : Bool) : Equiv.Perm (Fin 6) := if b then
  { toFun := ![2,3,4,0,5,1]
    invFun := ![3,5,0,1,2,4]
    left_inv := by decide
    right_inv := by decide }
  else
  { toFun := ![2,0,4,5,3,1]
    invFun := ![1,5,0,4,2,3]
    left_inv := by decide
    right_inv := by decide }

def leg (N : Network K 4) (b : Bool) : Network K 4 :=
  (C.reindex (C.tensor N (Network.corolla identity)) (order b)).contract Signature.disequality

def legWord (b : Bool) (x : Fin 4 → Bool) : Fin 4 → Bool :=
  if b then ![x 0,x 1,x 2,!(x 3)] else ![x 0,!(x 1),x 2,x 3]

theorem leg_denote (N : Network K 4) (b : Bool) :
    (leg N b).denote=fun x => N.denote (legWord b x) := by
  funext x
  rw [leg,Network.denote_contract_disequality,C.reindex_denote,C.tensor_denote,
    Network.denote_corolla]
  have eval (b u v : Bool) :
      Tensor.reindex (order b) (N.denote.tensor identity) (Fin.cons u (Fin.cons v x)) =
        if b then N.denote ![x 0,x 1,x 2,u] * Signature.equality (x 3) v
        else N.denote ![x 0,u,x 2,x 3] * Signature.equality (x 1) v := by
    cases b <;> dsimp [Tensor.reindex,Signature.tensor,order,identity]
    all_goals congr 1
    all_goals congr 1
    all_goals funext i; fin_cases i <;> rfl
  rw [eval,eval]
  cases b <;> cases h1 : x 1 <;> cases h3 : x 3 <;>
    simp [legWord,Signature.equality,h1,h3]

def identityLabels (j : Fin s) (arity : a j.val=2) :
    Labelling (Network.corolla (identity (K:=K))).shape s 1 a where
  vertex _ := j
  vertex_arity _ := arity
  edge e := Fin.elim0 e

def legLabels (N : Network K 4) (NL : Labelling N.shape s 1 a)
    (j : Fin s) (arity : a j.val=2) (b : Bool) : Labelling (leg N b).shape s 1 a :=
  LabelledNetwork.contract _ (LabelledNetwork.reindex _
    (LabelledNetwork.tensor N (Network.corolla identity) NL (identityLabels j arity)) (order b))
    0 Signature.disequality

theorem leg_exact (F : (i : Fin s) → Signature K (a i.val))
    (N : Network K 4) (NL : Labelling N.shape s 1 a) (exact : LabelledNetwork.Exact F N NL)
    (j : Fin s) (hj : (⟨a j.val,F j⟩ : AnySignature K)=⟨2,identity⟩) (b : Bool) :
    LabelledNetwork.Exact F (leg N b) (legLabels N NL j (congrArg Sigma.fst hj) b) := by
  change LabelledNetwork.Exact F (C.tensor N (Network.corolla identity))
    (LabelledNetwork.tensor N (Network.corolla identity) NL
      (identityLabels j (congrArg Sigma.fst hj)))
  exact LabelledNetwork.exact_tensor N (Network.corolla identity) NL
    (identityLabels j (congrArg Sigma.fst hj)) F exact (fun _ => hj)

theorem leg_native (N : Network K 4) (native : ∀e,N.edge e=Signature.disequality) (b : Bool) :
    ∀e,(leg N b).edge e=Signature.disequality := by
  intro e
  refine Fin.cases rfl (fun e => ?_) e
  change (Network.tensorFinite N (Network.corolla identity)).edge (finSumFinEquiv.symm e)=_
  cases finSumFinEquiv.symm e with
  | inl e => exact native e
  | inr e => exact Fin.elim0 e

theorem equality_denote (N : Network K 4) (c : K)
    (denote : N.denote=c • ExactTwoSignatures.E) :
    (leg (leg N false) true).denote=c • Holant.EightVertex.ProductAnchor.equalityFour := by
  rw [leg_denote,leg_denote,denote]
  funext x
  simp only [Pi.smul_apply,smul_eq_mul]
  congr 1
  rw [ExactTwoSignatures.E_reference]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [legWord,Holant.EightVertex.ProductAnchor.equalityFour,Fin.forall_fin_succ,h0,h1,h2,h3]

variable {r : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin r) → Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

def produce (D : GeneralEODEQProducerNormalize.Produced P.table) :
    GlobalCloseCompletionEq4Graph.Output G P := by
  let j := P.equality.choose
  have hj := P.equality.choose_spec
  have hi : (⟨P.arity j.val,P.table j⟩ : AnySignature (OI.K G))=⟨2,identity⟩ := hj
  let L := legLabels D.network D.labels j (congrArg Sigma.fst hi) false
  have hL := leg_exact P.table D.network D.labels D.exact j hi false
  exact ⟨leg (leg D.network false) true,
    legLabels (leg D.network false) L j (congrArg Sigma.fst hi) true,
    leg_exact P.table (leg D.network false) L hL j hi true,
    leg_native (leg D.network false) (leg_native D.network D.native false) true,
    D.scalar,D.nonzero,equality_denote D.network D.scalar D.denote⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSparseEq4Flip
end
