import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryFactorCaps

/-! With both literal pins, every nonzero retained factor has an actual
same-table graph at an internally selected complementary support pivot.
All zero/one choices are physical pin vertices; no coordinate flip is a gate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinFactors
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {K : Type} [Field K] {r n : ℕ} {a : ℕ→ℕ}

namespace F
export GlobalCloseCompletionUnaryFactorCaps (lastCap order)
end F

def word {n : ℕ} (x : Fin n→Bool) : (m : ℕ)→(Fin m→Bool)→Fin (n+m)→Bool
  | 0,_=>x
  | m+1,y=>Fin.snoc (word x m (fun i=>y i.castSucc)) (y (Fin.last m))

def graph (P : Bool→Network K 1) (n : ℕ) : (m : ℕ)→(Fin m→Bool)→Network K (n+m)→Network K n
  | 0,_,N=>N
  | m+1,y,N=>graph P n m (fun i=>y i.castSucc) (F.lastCap (P (y (Fin.last m))) N)

variable (P : Bool→Network K 1)
variable (pinForm : ∀v,(P v).denote=QuaternaryUnaryAccess.pin v)

include pinForm in
theorem last_value {n : ℕ} (N : Network K (n+1)) (v : Bool) (x : Fin n→Bool) :
    (F.lastCap (P v) N).denote x=N.denote (Fin.snoc x v) := by
  rw [F.lastCap,capHead_denote,pinForm]
  simp only [reboundary_denote]
  rw [Fin.snoc_eq_cons_rotate]
  cases v <;>simp [QuaternaryUnaryAccess.pin]

include pinForm in
theorem value (n m : ℕ) (y : Fin m→Bool) (N : Network K (n+m)) (x : Fin n→Bool) :
    (graph P n m y N).denote x=N.denote (word x m y) := by
  induction m with
  | zero=>rfl
  | succ m ih=>
    rw [graph,ih,last_value P pinForm]
    rfl

theorem word_left {n : ℕ} (x : Fin n→Bool) (m : ℕ) (y : Fin m→Bool) (i : Fin n) :
    word x m y (Fin.castAdd m i)=x i := by
  induction m with
  | zero=>rfl
  | succ m ih=>rw [word,Fin.snoc_castAdd,ih]

theorem word_right {n : ℕ} (x : Fin n→Bool) (m : ℕ) (y : Fin m→Bool) (i : Fin m) :
    word x m y (Fin.natAdd n i)=y i := by
  induction m with
  | zero=>exact Fin.elim0 i
  | succ m ih=>
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp [word]
    · simpa only [word,Fin.natAdd_castSucc,Fin.snoc_castSucc] using ih (fun k=>y k.castSucc) j

theorem uses (S : SignatureFamily K) (pUses : ∀v,Uses (P v) S) (n m : ℕ)
    (y : Fin m→Bool) (N : Network K (n+m)) (nUses : Uses N S) : Uses (graph P n m y N) S := by
  induction m with
  | zero=>exact nUses
  | succ m ih=>exact ih _ _ (capHead_uses S (P (y (Fin.last m))) _ (pUses _) nUses)

theorem ordinary (pEdges : ∀v,Ordinary (P v)) (n m : ℕ) (y : Fin m→Bool)
    (N : Network K (n+m)) (nEdges : Ordinary N) : Ordinary (graph P n m y N) := by
  induction m with
  | zero=>exact nEdges
  | succ m ih=>exact ih _ _ (capHead_ordinary (P (y (Fin.last m))) _ (pEdges _) nEdges)

variable (H : (j : Fin r)→Signature K (a j.val))
variable (pins : Bool→NoXOrdinaryGraphAdjoin.Output H 1) (N : NoXOrdinaryGraphAdjoin.Output H n)
variable {f g : AnySignature K} (s : ProperSplit (⟨n,N.network.denote⟩ : AnySignature K) f g)
variable (y : Fin g.1→Bool)

def factorGraph : Network K f.1 :=
  graph (fun v=>(pins v).network) f.1 g.1 y (reboundary N.network (F.order H N s))

def labels : Labelling (factorGraph H pins N s y).shape r 1 a :=
  let h:=uses (fun v=>(pins v).network) (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (fun v w=>⟨(pins v).labels.vertex w,(pins v).exact w⟩) f.1 g.1 y
    (reboundary N.network (F.order H N s)) (fun v=>⟨N.labels.vertex v,N.exact v⟩)
  {vertex v:=Classical.choose (h v)
   vertex_arity v:=congrArg Sigma.fst (Classical.choose_spec (h v))
   edge _:=0}

theorem exact : LabelledNetwork.Exact H (factorGraph H pins N s y) (labels H pins N s y) := by
  intro v
  exact Classical.choose_spec (uses (fun v=>(pins v).network)
    (Set.range fun j : Fin r=>(⟨a j.val,H j⟩ : AnySignature K))
    (fun v w=>⟨(pins v).labels.vertex w,(pins v).exact w⟩) f.1 g.1 y
    (reboundary N.network (F.order H N s)) (fun v=>⟨N.labels.vertex v,N.exact v⟩) v)

def output : NoXOrdinaryGraphAdjoin.Output H f.1 :=
  ⟨factorGraph H pins N s y,labels H pins N s y,exact H pins N s y,
    ordinary (fun v=>(pins v).network) (fun v=>(pins v).ordinary) f.1 g.1 y _ N.ordinary⟩

variable (pinsForm : ∀v,(pins v).network.denote=QuaternaryUnaryAccess.pin v)
include pinsForm in
theorem denote : (output H pins N s y).network.denote=fun x=>(s.scale : K)*g.2 y*f.2 x := by
  funext x
  change (factorGraph H pins N s y).denote x=_
  rw [factorGraph,value _ pinsForm,reboundary_denote]
  have eqn:=congrFun s.equation (fun i=>word x g.1 y (F.order H N s i))
  have hl : (fun i=>word x g.1 y (F.order H N s (s.ports (.inl i))))=x := by
    funext i;simp [F.order,word_left]
  have hr : (fun i=>word x g.1 y (F.order H N s (s.ports (.inr i))))=y := by
    funext i;simp [F.order,word_right]
  dsimp only at eqn
  rw [hl,hr] at eqn
  exact eqn.trans (by ring)

include pinsForm in
theorem exists_leaf (nonzero : N.network.denote≠0)
    (t : FactorTree (⟨n,N.network.denote⟩ : AnySignature K))
    (leaf : AnySignature K) (member : leaf∈t.leaves) :
    ∃V : NoXOrdinaryGraphAdjoin.Output H leaf.1,
      Prime (⟨leaf.1,V.network.denote⟩ : AnySignature K) ∧
      ∃c : K,c≠0 ∧ V.network.denote=(fun x=>c*leaf.2 x) := by
  have hp:=FactorTree.leaves_prime t leaf member
  rcases t.leaf_split leaf member with equal|⟨b,⟨split⟩⟩
  · subst leaf
    exact ⟨N,hp,1,one_ne_zero,by simp⟩
  · have existsPivot : ∃y,b.2 y≠0 := by
      by_contra none
      push Not at none
      exact (split.factors_nonzero nonzero).2 (funext none)
    obtain ⟨y,pivot⟩:=existsPivot
    let c:=(split.scale : K)*b.2 y
    have hc : c≠0:=mul_ne_zero split.scale.ne_zero pivot
    have eqn:=denote H pins N split y pinsForm
    refine ⟨output H pins N split y,?_,c,hc,eqn⟩
    rw [eqn]
    exact Holant.LocalDrafts.Hardness.FrozenFactorNormalization.prime_scaled (Units.mk0 c hc) hp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryBothPinFactors
end
