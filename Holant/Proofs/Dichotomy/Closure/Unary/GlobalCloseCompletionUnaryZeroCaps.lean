import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductTopPrime

/-! Actual repeated zero-pin caps expose any selected unary marginal.
Only copies of the given ordinary pin graph are used. Its scalar is kept
to the exact power, and all vertices, equality edges and labels are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroCaps
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {K : Type} [Field K]

def kept : (n : ℕ)→Bool→Fin (n+1)→Bool
  | 0,b=>fun _=>b
  | n+1,b=>Fin.cons false (kept n b)
def graph (U : Network K 1) : (n : ℕ)→Network K (n+1)→Network K 1
  | 0,N=>N
  | n+1,N=>graph U n (capHead U N)

theorem entry (U : Network K 1) (scalar : K)
    (pin0 : U.denote (fun _=>false)=scalar) (pin1 : U.denote (fun _=>true)=0)
    (n : ℕ) (N : Network K (n+1)) (x : Fin 1→Bool) :
    (graph U n N).denote x=scalar^n*N.denote (kept n (x 0)) := by
  induction n with
  | zero=>
    have hx : (fun _ : Fin 1=>x 0)=x := funext fun i=>congrArg x (Fin.eq_zero i).symm
    simp [graph,kept,hx]
  | succ n ih=>
    rw [graph,ih,capHead_denote,pin0,pin1]
    simp only [zero_mul,add_zero,kept,pow_succ]
    ring

theorem uses (F : SignatureFamily K) (U : Network K 1) (uUses : Uses U F)
    (n : ℕ) (N : Network K (n+1)) (nUses : Uses N F) : Uses (graph U n N) F := by
  induction n with
  | zero=>exact nUses
  | succ n ih=>exact ih (capHead U N) (capHead_uses F U N uUses nUses)

theorem ordinary (U : Network K 1) (uEdges : Ordinary U)
    (n : ℕ) (N : Network K (n+1)) (nEdges : Ordinary N) : Ordinary (graph U n N) := by
  induction n with
  | zero=>exact nEdges
  | succ n ih=>exact ih (capHead U N) (capHead_ordinary U N uEdges nEdges)

theorem counts (U : Network K 1) (n : ℕ) (N : Network K (n+1)) :
    (graph U n N).shape.vertices=n*U.shape.vertices+N.shape.vertices ∧
    (graph U n N).shape.edges=n*(U.shape.edges+1)+N.shape.edges := by
  induction n with
  | zero=>simp [graph]
  | succ n ih=>
    have h:=ih (capHead U N)
    rw [capHead_vertices,capHead_edges] at h
    constructor
    · exact h.1.trans (by ring)
    · exact h.2.trans (by ring)

theorem kept_product (n : ℕ) (w : Fin (n+1)→K) (b : Bool) :
    (∏i,if kept n b i then w i else 1)=if b then w (Fin.last n) else 1 := by
  induction n with
  | zero=>simp [kept]
  | succ n ih=>
    rw [Fin.prod_univ_succ]
    change (1 : K)*(∏i,if kept n b i then w i.succ else 1)=_
    rw [one_mul]
    rw [ih]
    rfl

theorem kept_not_top (n : ℕ) (positive : 0<n) (b : Bool) : kept n b≠(fun _=>true) := by
  cases n with
  | zero=>omega
  | succ n=>
    intro h
    have hh:=congrFun h 0
    simp [kept] at hh

theorem productTop_entry (U : Network K 1) (scalar : K)
    (pin0 : U.denote (fun _=>false)=scalar) (pin1 : U.denote (fun _=>true)=0)
    (n : ℕ) (positive : 0<n) (N : Network K (n+1)) (w : Fin (n+1)→K) (c d : K)
    (form : N.denote=GlobalCloseCompletionUnaryProductTopPrime.value w c d) :
    (graph U n N).denote=fun x=>scalar^n*c*(if x 0 then w (Fin.last n) else 1) := by
  classical
  funext x
  rw [entry U scalar pin0 pin1 n N x,form]
  simp only [GlobalCloseCompletionUnaryProductTopPrime.value,kept_not_top n positive,
    ite_false,add_zero,kept_product]
  ring

variable {r : ℕ} {a : ℕ→ℕ} (H : (i : Fin r)→Signature K (a i.val))
variable (U : Network K 1) (UL : Labelling U.shape r 1 a)
variable (uExact : LabelledNetwork.Exact H U UL)
variable (n : ℕ) (N : Network K (n+1)) (NL : Labelling N.shape r 1 a)
variable (nExact : LabelledNetwork.Exact H N NL)

def labels : Labelling (graph U n N).shape r 1 a :=
  let hf:=uses (Set.range fun i : Fin r=>(⟨a i.val,H i⟩ : AnySignature K)) U
    (fun v=>⟨UL.vertex v,uExact v⟩) n N (fun v=>⟨NL.vertex v,nExact v⟩)
  {vertex v:=Classical.choose (hf v)
   vertex_arity v:=congrArg Sigma.fst (Classical.choose_spec (hf v))
   edge _:=0}

theorem exact : LabelledNetwork.Exact H (graph U n N) (labels H U UL uExact n N NL nExact) := by
  intro v
  exact Classical.choose_spec (uses (Set.range fun i : Fin r=>(⟨a i.val,H i⟩ : AnySignature K)) U
    (fun v=>⟨UL.vertex v,uExact v⟩) n N (fun v=>⟨NL.vertex v,nExact v⟩) v)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryZeroCaps
end
