import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryEndpointEq4
import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryJoin

/-! Every genuine native endpoint-only resource of arity at least three
supplies equality-four. Two copies use exactly n-2 parallel native-X edges;
the first two ports of each copy survive. Existing endpoint Fubini evaluation
is reused, with exact finite original labels added here. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryHigherEq4
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace J
export GeneralOddHigherResidueQuaternaryPartialJoin (network finite Edges denote vertices edges)
end J
namespace T
export GeneralOddHigherResidueQuaternaryJoin (nativeTable zeroOne oneZero native_value)
end T
namespace C
export BinaryInterpolation.Chains (reindex reindex_denote)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 8192
set_option Elab.async false
variable {K : Type} [Field K] {s k : ℕ} {a : ℕ → ℕ}

def endpoint (n : ℕ) (A B : K) : Signature K n := purePin A false n+purePin B true n

/-- Support, rather than a preselected coefficient formula, determines the
weighted endpoint row. The two weights are the actual network coefficients. -/
theorem endpoint_of_support (f : Signature K (k+2))
    (support : ∀x,f x≠0 → x=(fun _=>false) ∨ x=(fun _=>true)) :
    f=endpoint (k+2) (f (fun _=>false)) (f (fun _=>true)) := by
  classical
  have distinct : (fun _ : Fin (k+2)=>false)≠(fun _=>true) := by
    intro h
    have := congrFun h 0
    contradiction
  funext x
  by_cases h0 : x=(fun _=>false)
  · subst x
    simp [endpoint,purePin,distinct]
  by_cases h1 : x=(fun _=>true)
  · subst x
    simp [endpoint,purePin,h0]
  have hx : f x=0 := by
    by_contra hn
    exact (support x hn).elim h0 h1
  simp [endpoint,purePin,h0,h1,hx]

def swap : Equiv.Perm (Fin 4) := Equiv.swap 1 2

theorem reordered (c : K) : Tensor.reindex swap (T.nativeTable c)=c • ExactTwoSignatures.E := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex_apply,swap,Equiv.swap_apply_def,T.nativeTable,T.zeroOne,T.oneZero,
      funext_iff,Fin.forall_fin_succ,Pi.smul_apply,smul_eq_mul,ExactTwoSignatures.E_reference,
      h0,h1,h2,h3]

def parallel (N : Network K (k+2)) : Network K 4 :=
  J.network N N (fun _=>Signature.disequality)

def graph (N : Network K (k+2)) : Network K 4 := C.reindex (parallel N) swap

def parallelLabels (N : Network K (k+2)) (NL : Labelling N.shape s 1 a) :
    Labelling (parallel N).shape s 1 a where
  vertex v := Sum.elim NL.vertex NL.vertex
    ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.vertices)).symm v)
  vertex_arity v := by
    change a (Sum.elim NL.vertex NL.vertex
      ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.vertices)).symm v)).val=
        Sum.elim N.shape.arity N.shape.arity
          ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.vertices)).symm v)
    generalize (Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.vertices)).symm v=w
    cases w with
    | inl i => exact NL.vertex_arity i
    | inr i => exact NL.vertex_arity i
  edge _ := 0

def labels (N : Network K (k+2)) (NL : Labelling N.shape s 1 a) :
    Labelling (graph N).shape s 1 a := LabelledNetwork.reindex _ (parallelLabels N NL) swap

theorem exact (F : (i : Fin s) → Signature K (a i.val))
    (N : Network K (k+2)) (NL : Labelling N.shape s 1 a)
    (hN : LabelledNetwork.Exact F N NL) : LabelledNetwork.Exact F (graph N) (labels N NL) := by
  intro v
  change (⟨a (Sum.elim NL.vertex NL.vertex
      ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.vertices)).symm v)).val,
    F (Sum.elim NL.vertex NL.vertex
      ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.vertices)).symm v))⟩ : AnySignature K)=
    ⟨_,(J.finite N N (fun _=>Signature.disequality)).vertex
      ((Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.vertices)).symm v)⟩
  generalize (Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.vertices)).symm v=w
  cases w with
  | inl i => exact hN i
  | inr i => exact hN i

theorem native (N : Network K (k+2)) (hN : ∀e,N.edge e=Signature.disequality) :
    ∀e,(graph N).edge e=Signature.disequality := by
  intro e
  change (J.finite N N (fun _=>Signature.disequality)).edge
    ((Fintype.equivFin (J.Edges N N)).symm e)=Signature.disequality
  generalize (Fintype.equivFin (J.Edges N N)).symm e=w
  rcases w with (i|i)|i
  · exact hN i
  · exact hN i
  · rfl

theorem denote (N : Network K (k+2)) (hk : 0<k) (A B : K)
    (hN : N.denote=endpoint (k+2) A B) :
    (graph N).denote=(A*B) • ExactTwoSignatures.E := by
  rw [graph,C.reindex_denote,parallel,J.denote,hN,endpoint,T.native_value hk,reordered]

theorem counts (N : Network K (k+2)) :
    (graph N).shape.vertices=2*N.shape.vertices ∧
    (graph N).shape.edges=2*N.shape.edges+k := by
  change (parallel N).shape.vertices=_ ∧ (parallel N).shape.edges=_
  rw [parallel,J.vertices,J.edges]
  constructor <;> omega

def central (F : (i : Fin s) → Signature K (a i.val))
    (N : Network K (k+2)) (NL : Labelling N.shape s 1 a)
    (hE : LabelledNetwork.Exact F N NL) (hX : ∀e,N.edge e=Signature.disequality)
    (hk : 0<k) (support : ∀x,N.denote x≠0 → x=(fun _=>false) ∨ x=(fun _=>true))
    (h0 : N.denote (fun _=>false)≠0) (h1 : N.denote (fun _=>true)≠0) :
    GeneralEODEQProducerNormalize.Produced F :=
  ⟨graph N,labels N NL,exact F N NL hE,native N hX,_,mul_ne_zero h0 h1,
    denote N hk _ _ (endpoint_of_support N.denote support)⟩

variable {r : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin r) → Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

def produce (N : Network (OI.K G) (k+2)) (NL : Labelling N.shape P.count 1 P.arity)
    (hE : LabelledNetwork.Exact P.table N NL) (hX : ∀e,N.edge e=Signature.disequality)
    (hk : 0<k) (support : ∀x,N.denote x≠0 → x=(fun _=>false) ∨ x=(fun _=>true))
    (h0 : N.denote (fun _=>false)≠0) (h1 : N.denote (fun _=>true)≠0) :
    GlobalCloseCompletionEq4Graph.Output G P :=
  GlobalCloseCompletionSparseEq4Flip.produce G P (central P.table N NL hE hX hk support h0 h1)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryHigherEq4
end
