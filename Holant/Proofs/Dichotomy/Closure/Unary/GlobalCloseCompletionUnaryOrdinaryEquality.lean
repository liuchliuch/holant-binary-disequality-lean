import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryHigherEq4

/-! Ordinary endpoint resources produce a weighted equality-four and exact
positive power chains. A finite endpoint-weight ratio yields actual Eq4;
an infinite ratio is retained as an exact geometric interpolation family.
No inverse-weight unary is assumed to be physically available. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryOrdinaryEquality
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
open scoped BigOperators
namespace J
export GeneralOddHigherResidueQuaternaryPartialJoin
  (network finite Edges denote vertices edges value value_add_left value_add_right)
end J
namespace T
export GeneralOddHigherResidueQuaternaryJoin (value_pins halves_iff)
end T
namespace C
export BinaryInterpolation.Chains (tensor tensor_denote reindex reindex_denote)
end C
export GlobalCloseCompletionUnaryHigherEq4 (endpoint endpoint_of_support)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 8192
set_option Elab.async false
variable {K : Type} [Field K] {s k : ℕ} {a : ℕ → ℕ}

/-- Opposite endpoints vanish along an ordinary equality edge, so the two
surviving weights are squared rather than implicitly cancelled. -/
theorem join_value (hk : 0<k) (A B : K) :
    J.value (fun _ : Fin k=>Signature.equality) (endpoint (k+2) A B)
      (endpoint (k+2) A B)=endpoint 4 (A^2) (B^2) := by
  simp only [endpoint,J.value_add_left,J.value_add_right,T.value_pins]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Signature.equality,hk.ne',GeneralOddHigherResidueQuaternaryPartialJoin.left,
      GeneralOddHigherResidueQuaternaryPartialJoin.right,purePin,funext_iff,Fin.forall_fin_succ,
      h0,h1,h2,h3,pow_two]

def joined (N : Network K (k+2)) : Network K 4 :=
  J.network N N (fun _=>Signature.equality)

theorem joined_denote (N : Network K (k+2)) (hk : 0<k) (A B : K)
    (hN : N.denote=endpoint (k+2) A B) :
    (joined N).denote=endpoint 4 (A^2) (B^2) := by
  rw [joined,J.denote,hN,join_value hk]

def joinLabels (N : Network K (k+2)) (NL : Labelling N.shape s 1 a) :
    Labelling (joined N).shape s 1 a := GlobalCloseCompletionUnaryHigherEq4.parallelLabels N NL

theorem joined_exact (F : (i : Fin s) → Signature K (a i.val))
    (N : Network K (k+2)) (NL : Labelling N.shape s 1 a)
    (hN : LabelledNetwork.Exact F N NL) :
    LabelledNetwork.Exact F (joined N) (joinLabels N NL) :=
  GlobalCloseCompletionUnaryHigherEq4.exact F N NL hN

theorem joined_ordinary (N : Network K (k+2)) (hN : ∀e,N.edge e=Signature.equality) :
    ∀e,(joined N).edge e=Signature.equality := by
  intro e
  change (J.finite N N (fun _=>Signature.equality)).edge
    ((Fintype.equivFin (J.Edges N N)).symm e)=Signature.equality
  generalize (Fintype.equivFin (J.Edges N N)).symm e=w
  rcases w with (i|i)|i
  · exact hN i
  · exact hN i
  · rfl

/-- Ports 1 and 3 of the left copy join ports 0 and 2 of the right copy. -/
def order : Equiv.Perm (Fin 8) where
  toFun := ![4,0,6,2,1,5,3,7]
  invFun := ![1,4,3,6,0,5,2,7]
  left_inv := by decide
  right_inv := by decide

def series (N M : Network K 4) : Network K 4 :=
  ((C.reindex (C.tensor N M) order).contract Signature.equality).contract Signature.equality

theorem series_value (N M : Network K 4) (x : Fin 4→Bool) :
    (series N M).denote x=∑u : Bool,∑v : Bool,
      N.denote ![x 0,u,x 2,v]*M.denote ![u,x 1,v,x 3] := by
  rw [series,Network.denote_contract,Network.denote_contract,C.reindex_denote,C.tensor_denote]
  simp only [Signature.contract_equality,Tensor.reindex_apply,Signature.tensor_apply]
  have hl (a b c d : Bool) :
      (fun i : Fin 4=>(Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d x))) : Fin 8→Bool)
        (order (Fin.castAdd 4 i)))=![x 0,a,x 2,c] := by
    funext i; fin_cases i <;> rfl
  have hr (a b c d : Bool) :
      (fun i : Fin 4=>(Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d x))) : Fin 8→Bool)
        (order (Fin.natAdd 4 i)))=![b,x 1,d,x 3] := by
    funext i; fin_cases i <;> rfl
  simp only [hl,hr,Fintype.sum_bool]
  ring

theorem series_denote (N M : Network K 4) (A B C D : K)
    (hN : N.denote=endpoint 4 A B) (hM : M.denote=endpoint 4 C D) :
    (series N M).denote=endpoint 4 (A*C) (B*D) := by
  funext x
  rw [series_value,hN,hM]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [endpoint,purePin,funext_iff,Fin.forall_fin_succ,Fintype.sum_bool,h0,h1,h2,h3]

def seriesLabels (N M : Network K 4) (NL : Labelling N.shape s 1 a)
    (ML : Labelling M.shape s 1 a) : Labelling (series N M).shape s 1 a :=
  LabelledNetwork.contract _ (LabelledNetwork.contract _
    (LabelledNetwork.reindex _ (LabelledNetwork.tensor N M NL ML) order)
    0 Signature.equality) 0 Signature.equality

theorem series_exact (F : (i : Fin s) → Signature K (a i.val))
    (N M : Network K 4) (NL : Labelling N.shape s 1 a) (ML : Labelling M.shape s 1 a)
    (hN : LabelledNetwork.Exact F N NL) (hM : LabelledNetwork.Exact F M ML) :
    LabelledNetwork.Exact F (series N M) (seriesLabels N M NL ML) :=
  LabelledNetwork.exact_tensor N M NL ML F hN hM

theorem series_ordinary (N M : Network K 4)
    (hN : ∀e,N.edge e=Signature.equality) (hM : ∀e,M.edge e=Signature.equality) :
    ∀e,(series N M).edge e=Signature.equality := by
  intro e
  refine Fin.cases rfl (fun e=>Fin.cases rfl (fun e=>?_) e) e
  change (Network.tensorFinite N M).edge (finSumFinEquiv.symm e)=_
  cases finSumFinEquiv.symm e with
  | inl e => exact hN e
  | inr e => exact hM e

def power (N : Network K 4) : ℕ→Network K 4
  | 0=>N
  | t+1=>series N (power N t)

theorem power_denote (N : Network K 4) (A B : K) (hN : N.denote=endpoint 4 A B)
    (t : ℕ) : (power N t).denote=endpoint 4 (A^(t+1)) (B^(t+1)) := by
  induction t with
  | zero=>simpa only [power,Nat.zero_add,pow_one] using hN
  | succ t ih=>simpa only [power,pow_succ,mul_comm] using series_denote N (power N t) A B _ _ hN ih

def powerLabels (N : Network K 4) (NL : Labelling N.shape s 1 a) :
    (t : ℕ)→Labelling (power N t).shape s 1 a
  | 0=>NL
  | t+1=>seriesLabels N (power N t) NL (powerLabels N NL t)

theorem power_exact (F : (i : Fin s)→Signature K (a i.val))
    (N : Network K 4) (NL : Labelling N.shape s 1 a)
    (hN : LabelledNetwork.Exact F N NL) (t : ℕ) :
    LabelledNetwork.Exact F (power N t) (powerLabels N NL t) := by
  induction t with
  | zero=>exact hN
  | succ t ih=>exact series_exact F N (power N t) NL (powerLabels N NL t) hN ih

theorem power_ordinary (N : Network K 4) (hN : ∀e,N.edge e=Signature.equality) (t : ℕ) :
    ∀e,(power N t).edge e=Signature.equality := by
  induction t with
  | zero=>exact hN
  | succ t ih=>exact series_ordinary N (power N t) hN ih

theorem power_counts (N : Network K 4) (t : ℕ) :
    (power N t).shape.vertices=(t+1)*N.shape.vertices ∧
    (power N t).shape.edges=(t+1)*N.shape.edges+2*t := by
  induction t with
  | zero=>constructor <;> simp [power]
  | succ t ih=>
    change N.shape.vertices+(power N t).shape.vertices=_ ∧
      (N.shape.edges+(power N t).shape.edges+1)+1=_
    rw [ih.1,ih.2]
    constructor <;> ring

theorem period_denote (N : Network K 4) (A B : K) (hA : A≠0)
    (hN : N.denote=endpoint 4 A B) (t : ℕ) (ht : 0<t) (period : (B/A)^t=1) :
    (power N (t-1)).denote=A^t • Holant.EightVertex.ProductAnchor.equalityFour := by
  have exp : t-1+1=t := by omega
  have eq : B^t=A^t := (div_eq_one_iff_eq (pow_ne_zero t hA)).mp (by simpa [div_pow] using period)
  rw [power_denote N A B hN,exp,eq]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [endpoint,purePin,Holant.EightVertex.ProductAnchor.equalityFour,
      funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryOrdinaryEquality
end
