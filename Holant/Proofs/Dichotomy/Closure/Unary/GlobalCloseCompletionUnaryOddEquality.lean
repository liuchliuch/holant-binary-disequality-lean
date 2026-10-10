import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryOrdinaryEquality

/-! Genuine ordinary loops reduce every odd endpoint resource of arity at
least three to weighted equality-three. Both endpoint coefficients and every
original label survive exactly; the added loop count is explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryOddEquality
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace W
export GlobalCloseCompletionUnaryOrdinaryEquality (endpoint)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 8192
set_option Elab.async false
variable {K : Type} [Field K] {s n m : ℕ} {a : ℕ→ℕ}

theorem cast_denote (N : Network K n) (h : n=m) (A B : K)
    (hN : N.denote=W.endpoint n A B) :
    (reboundary N (finCongr h)).denote=W.endpoint m A B := by
  cases h
  funext x
  rw [reboundary_denote]
  exact congrFun hN x

theorem contract_denote (N : Network K (n+2)) (A B : K)
    (hN : N.denote=W.endpoint (n+2) A B) :
    (N.contract Signature.equality).denote=W.endpoint n A B := by
  rw [Network.denote_contract,hN]
  funext x
  rw [Signature.contract_equality]
  simp [W.endpoint,purePin,funext_iff,Fin.forall_fin_succ]

def step (j : ℕ) (N : Network K (2*(j+1)+3)) : Network K (2*j+3) :=
  (reboundary N (finCongr (by omega : 2*(j+1)+3=(2*j+3)+2))).contract Signature.equality

def reduce : (j : ℕ)→Network K (2*j+3)→Network K 3
  | 0,N=>N
  | j+1,N=>reduce j (step j N)

theorem denote (j : ℕ) (N : Network K (2*j+3)) (A B : K)
    (hN : N.denote=W.endpoint (2*j+3) A B) :
    (reduce j N).denote=W.endpoint 3 A B := by
  induction j with
  | zero=>exact hN
  | succ j ih=>
    exact ih (step j N) (contract_denote _ A B (cast_denote N _ A B hN))

def stepLabels (j : ℕ) (N : Network K (2*(j+1)+3)) (NL : Labelling N.shape s 1 a) :
    Labelling (step j N).shape s 1 a where
  vertex := NL.vertex
  vertex_arity := NL.vertex_arity
  edge := Fin.cons 0 NL.edge

def labels : (j : ℕ)→(N : Network K (2*j+3))→(NL : Labelling N.shape s 1 a)→
    Labelling (reduce j N).shape s 1 a
  | 0,_,NL=>NL
  | j+1,N,NL=>labels j (step j N) (stepLabels j N NL)

theorem exact (F : (i : Fin s)→Signature K (a i.val))
    (j : ℕ) (N : Network K (2*j+3)) (NL : Labelling N.shape s 1 a)
    (hN : LabelledNetwork.Exact F N NL) :
    LabelledNetwork.Exact F (reduce j N) (labels j N NL) := by
  induction j with
  | zero=>exact hN
  | succ j ih=>exact ih (step j N) (stepLabels j N NL) hN

theorem ordinary (j : ℕ) (N : Network K (2*j+3))
    (hN : ∀e,N.edge e=Signature.equality) :
    ∀e,(reduce j N).edge e=Signature.equality := by
  induction j with
  | zero=>exact hN
  | succ j ih=>
    apply ih (step j N)
    intro e
    exact Fin.cases rfl (fun e=>hN e) e

theorem counts (j : ℕ) (N : Network K (2*j+3)) :
    (reduce j N).shape.vertices=N.shape.vertices ∧
    (reduce j N).shape.edges=N.shape.edges+j := by
  induction j with
  | zero=>constructor <;> simp [reduce]
  | succ j ih=>
    have h := ih (step j N)
    change (reduce j (step j N)).shape.vertices=_ ∧ (reduce j (step j N)).shape.edges=_
    rw [h.1,h.2]
    constructor
    · rfl
    · change (N.shape.edges+1)+j=N.shape.edges+(j+1)
      omega

/-- One additional genuine loop supplies the full unary needed by an
odd-interface hardness block. It uses only copies already in the graph. -/
def unary (j : ℕ) (N : Network K (2*j+3)) : Network K 1 :=
  (reduce j N).contract Signature.equality

def unaryLabels (j : ℕ) (N : Network K (2*j+3)) (NL : Labelling N.shape s 1 a) :
    Labelling (unary j N).shape s 1 a :=
  LabelledNetwork.contract (reduce j N) (labels j N NL) 0 Signature.equality

theorem unary_denote (j : ℕ) (N : Network K (2*j+3)) (A B : K)
    (hN : N.denote=W.endpoint (2*j+3) A B) :
    (unary j N).denote=W.endpoint 1 A B :=
  contract_denote (reduce j N) A B (denote j N A B hN)

theorem unary_literal (j : ℕ) (N : Network K (2*j+3)) (A B : K)
    (hN : N.denote=W.endpoint (2*j+3) A B) :
    (unary j N).denote=fun x=>if x 0 then B else A := by
  rw [unary_denote j N A B hN]
  funext x
  cases h : x 0 <;> simp [W.endpoint,purePin,funext_iff,Fin.forall_fin_succ,h]

theorem unary_exact (F : (i : Fin s)→Signature K (a i.val))
    (j : ℕ) (N : Network K (2*j+3)) (NL : Labelling N.shape s 1 a)
    (hN : LabelledNetwork.Exact F N NL) :
    LabelledNetwork.Exact F (unary j N) (unaryLabels j N NL) := exact F j N NL hN

theorem unary_ordinary (j : ℕ) (N : Network K (2*j+3))
    (hN : ∀e,N.edge e=Signature.equality) :
    ∀e,(unary j N).edge e=Signature.equality :=
  fun e=>Fin.cases rfl (fun e=>ordinary j N hN e) e

theorem unary_full (j : ℕ) (N : Network K (2*j+3)) (A B : K)
    (hN : N.denote=W.endpoint (2*j+3) A B) (hA : A≠0) (hB : B≠0) :
    ∀x,(unary j N).denote x≠0 := by
  rw [unary_denote j N A B hN]
  intro x
  cases h : x 0 <;> simp [W.endpoint,purePin,funext_iff,Fin.forall_fin_succ,h,hA,hB]

theorem unary_counts (j : ℕ) (N : Network K (2*j+3)) :
    (unary j N).shape.vertices=N.shape.vertices ∧
    (unary j N).shape.edges=N.shape.edges+(j+1) := by
  have h := counts j N
  change (reduce j N).shape.vertices=_ ∧ (reduce j N).shape.edges+1=_
  rw [h.1,h.2]
  exact ⟨rfl,by omega⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryOddEquality
end
