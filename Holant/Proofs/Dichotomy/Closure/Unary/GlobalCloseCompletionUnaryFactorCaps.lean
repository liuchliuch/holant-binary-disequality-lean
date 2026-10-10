import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroCaps
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOrdinaryGraphAdjoin
import Holant.Proofs.FiniteGroups.Stabilization.LeafExposure
import Holant.Proofs.Reductions.FrozenFactorNormalization.NormalizedTree
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Live-origin factors are physical in the presence of an actual zero pin.
The complementary ports are capped with that same pin, retaining its scalar
at every occurrence. This avoids treating a mathematical factor as a label
or calling a general factor oracle during unary descent. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryFactorCaps
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}

def lastCap (U : Network K 1) {n : ℕ} (N : Network K (n+1)) : Network K n :=
  capHead U (reboundary N (finRotate (n+1)))

def kept {n : ℕ} (x : Fin n→Bool) : (m : ℕ)→Fin (n+m)→Bool
  | 0=>x
  | m+1=>Fin.snoc (kept x m) false

def graph (U : Network K 1) (n : ℕ) : (m : ℕ)→Network K (n+m)→Network K n
  | 0,N=>N
  | m+1,N=>graph U n m (lastCap U N)

section Caps
variable (U : Network K 1) (scalar : K)
variable (pin0 : U.denote (fun _=>false)=scalar) (pin1 : U.denote (fun _=>true)=0)
include pin0 pin1 in
theorem last_value {n : ℕ} (N : Network K (n+1)) (x : Fin n→Bool) :
    (lastCap U N).denote x=scalar*N.denote (Fin.snoc x false) := by
  rw [lastCap,capHead_denote,pin0,pin1,reboundary_denote]
  rw [←Fin.snoc_eq_cons_rotate]
  simp

include pin0 pin1 in
theorem value (n m : ℕ) (N : Network K (n+m)) (x : Fin n→Bool) :
    (graph U n m N).denote x=scalar^m*N.denote (kept x m) := by
  induction m with
  | zero=>simp [graph,kept]
  | succ m ih=>
    rw [graph,ih,last_value U scalar pin0 pin1]
    simp only [kept,pow_succ]
    ring

theorem kept_left {n : ℕ} (x : Fin n→Bool) (m : ℕ) (i : Fin n) : kept x m (Fin.castAdd m i)=x i := by
  induction m with
  | zero=>rfl
  | succ m ih=>rw [kept,Fin.snoc_castAdd,ih]

theorem kept_right {n : ℕ} (x : Fin n→Bool) (m : ℕ) (i : Fin m) : kept x m (Fin.natAdd n i)=false := by
  induction m with
  | zero=>exact Fin.elim0 i
  | succ m ih=>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp [kept]
    · simpa only [kept,Fin.natAdd_castSucc,Fin.snoc_castSucc] using ih j

theorem uses (F : SignatureFamily K) (uUses : Uses U F) (n m : ℕ)
    (N : Network K (n+m)) (nUses : Uses N F) : Uses (graph U n m N) F := by
  induction m with
  | zero=>exact nUses
  | succ m ih=>exact ih (lastCap U N) (capHead_uses F U _ uUses nUses)

theorem ordinary (uEdges : Ordinary U) (n m : ℕ) (N : Network K (n+m)) (nEdges : Ordinary N) :
    Ordinary (graph U n m N) := by
  induction m with
  | zero=>exact nEdges
  | succ m ih=>exact ih (lastCap U N) (capHead_ordinary U _ uEdges nEdges)

end Caps
variable (H : (j : Fin r)→Signature K (a j.val))
variable (Up : NoXOrdinaryGraphAdjoin.Output H 1) (N : NoXOrdinaryGraphAdjoin.Output H n)
variable {f g : AnySignature K} (s : ProperSplit (⟨n,N.network.denote⟩ : AnySignature K) f g)

def order : Fin n≃Fin (f.1+g.1) := s.ports.symm.trans finSumFinEquiv

def factorGraph : Network K f.1 := graph Up.network f.1 g.1 (reboundary N.network (order H N s))

def labels : Labelling (factorGraph H Up N s).shape r 1 a :=
  let hf:=uses Up.network (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (fun v=>⟨Up.labels.vertex v,Up.exact v⟩) f.1 g.1 (reboundary N.network (order H N s))
    (fun v=>⟨N.labels.vertex v,N.exact v⟩)
  {vertex v:=Classical.choose (hf v)
   vertex_arity v:=congrArg Sigma.fst (Classical.choose_spec (hf v))
   edge _:=0}

theorem exact : LabelledNetwork.Exact H (factorGraph H Up N s) (labels H Up N s) := by
  intro v
  exact Classical.choose_spec (uses Up.network (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (fun v=>⟨Up.labels.vertex v,Up.exact v⟩) f.1 g.1 (reboundary N.network (order H N s))
    (fun v=>⟨N.labels.vertex v,N.exact v⟩) v)

def output : NoXOrdinaryGraphAdjoin.Output H f.1 :=
  ⟨factorGraph H Up N s,labels H Up N s,exact H Up N s,
    ordinary Up.network Up.ordinary f.1 g.1 _ N.ordinary⟩

theorem denote (scalar : K) (pin0 : Up.network.denote (fun _=>false)=scalar)
    (pin1 : Up.network.denote (fun _=>true)=0) :
    (output H Up N s).network.denote=fun x=>scalar^g.1*(s.scale : K)*g.2 (fun _=>false)*f.2 x := by
  funext x
  rw [show (output H Up N s).network.denote x=(factorGraph H Up N s).denote x from rfl,
    factorGraph,value Up.network scalar pin0 pin1,reboundary_denote]
  have eqn:=congrFun s.equation (fun i=>kept x g.1 (order H N s i))
  have hl : (fun i=>kept x g.1 (order H N s (s.ports (.inl i))))=x := by
    funext i
    simp [order,kept_left]
  have hr : (fun i=>kept x g.1 (order H N s (s.ports (.inr i))))=(fun _=>false) := by
    funext i
    simp [order,kept_right]
  dsimp only at eqn
  rw [hl,hr] at eqn
  rw [eqn]
  ring

include s in
theorem right_origin (origin : N.network.denote (fun _=>false)≠0) : g.2 (fun _=>false)≠0 := by
  intro zero
  apply origin
  have h:=congrFun s.equation (fun _=>false)
  simpa only [zero,mul_zero] using h

include s in
theorem left_origin (origin : N.network.denote (fun _=>false)≠0) : f.2 (fun _=>false)≠0 := by
  intro zero
  apply origin
  have h:=congrFun s.equation (fun _=>false)
  simpa only [zero,zero_mul,mul_zero] using h

variable (scalar : K) (scalarNonzero : scalar≠0)
variable (pin0 : Up.network.denote (fun _=>false)=scalar)
variable (pin1 : Up.network.denote (fun _=>true)=0)
variable (origin : N.network.denote (fun _=>false)≠0)
include scalarNonzero pin0 pin1 origin in
theorem exists_leaf (t : FactorTree (⟨n,N.network.denote⟩ : AnySignature K))
    (leaf : AnySignature K) (member : leaf∈t.leaves) :
    ∃V : NoXOrdinaryGraphAdjoin.Output H leaf.1,
      Prime (⟨leaf.1,V.network.denote⟩ : AnySignature K) ∧ V.network.denote (fun _=>false)≠0 ∧
      ∃c : K,c≠0 ∧ V.network.denote=(fun x=>c*leaf.2 x) := by
  have hp:=FactorTree.leaves_prime t leaf member
  rcases t.leaf_split leaf member with equal|⟨b,⟨split⟩⟩
  · subst leaf
    exact ⟨N,hp,origin,1,one_ne_zero,by simp⟩
  · let c:=scalar^b.1*(split.scale : K)*b.2 (fun _=>false)
    have hc : c≠0 := mul_ne_zero (mul_ne_zero (pow_ne_zero _ scalarNonzero) split.scale.ne_zero)
      (right_origin H N split origin)
    have eqn:=denote H Up N split scalar pin0 pin1
    have left:=left_origin H N split origin
    refine ⟨output H Up N split,?_,?_,c,hc,eqn⟩
    · rw [eqn]
      exact Holant.LocalDrafts.Hardness.FrozenFactorNormalization.prime_scaled (Units.mk0 c hc) hp
    · rw [eqn]
      exact mul_ne_zero hc left

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryFactorCaps
end
