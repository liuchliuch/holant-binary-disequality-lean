import Holant.Proofs.FiniteGroups.Stabilization.OccurrenceSchedule.Stored

/-! RECONSTRUCTED ordinary constructor data and counted tree ledgers.
Only the exact stored leaf/split is consumed; equal occurrences stay counted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.TokenExecution
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
variable {L : Type*} [Field L]
attribute [local instance] Classical.propDecidable

def nodeOccurrences {f : AnySignature L} : FactorTree f → Multiset (TreeOccurrence L)
  | .leaf f hp => {⟨f,.leaf f hp⟩}
  | .split sp l r => {⟨_,.split sp l r⟩} + nodeOccurrences l + nodeOccurrences r

def closedLeaves (t : TreeOccurrence L) : Multiset (TreeOccurrence L) :=
  if 2 ≤ t.1.1 then 0 else leafOccurrences t.2

def closedNodes (t : TreeOccurrence L) : Multiset (TreeOccurrence L) :=
  if 2 ≤ t.1.1 then 0 else nodeOccurrences t.2

def frontierLeaves (W : Multiset (TreeOccurrence L)) : Multiset (TreeOccurrence L) :=
  W.bind (fun t => leafOccurrences t.2)

def frontierNodes (W : Multiset (TreeOccurrence L)) : Multiset (TreeOccurrence L) :=
  W.bind (fun t => nodeOccurrences t.2)

theorem open_closed_leaves (t : TreeOccurrence L) :
    frontierLeaves (openTree t) + closedLeaves t = leafOccurrences t.2 := by
  by_cases h : 2 ≤ t.1.1 <;> simp [frontierLeaves,openTree,closedLeaves,h]

theorem open_closed_nodes (t : TreeOccurrence L) :
    frontierNodes (openTree t) + closedNodes t = nodeOccurrences t.2 := by
  by_cases h : 2 ≤ t.1.1 <;> simp [frontierNodes,openTree,closedNodes,h]

inductive TreeTransition : Multiset (TreeOccurrence L) → Multiset (TreeOccurrence L) → Type _
  | leaf (f : AnySignature L) (hp : Prime f) (hn : 2 ≤ f.1) (rest : Multiset (TreeOccurrence L)) :
      TreeTransition (⟨f,.leaf f hp⟩ ::ₘ rest) rest
  | split {f a b : AnySignature L} (sp : ProperSplit f a b) (l : FactorTree a) (r : FactorTree b)
      (rest : Multiset (TreeOccurrence L)) :
      TreeTransition (⟨f,.split sp l r⟩ ::ₘ rest) (openTree ⟨a,l⟩ + openTree ⟨b,r⟩ + rest)

def TreeTransition.focus {V W : Multiset (TreeOccurrence L)} : TreeTransition V W → TreeOccurrence L
  | .leaf f hp _ _ => ⟨f,.leaf f hp⟩
  | .split sp l r _ => ⟨_,.split sp l r⟩

def TreeTransition.exposed {V W : Multiset (TreeOccurrence L)} : TreeTransition V W → Multiset (TreeOccurrence L)
  | .leaf f hp _ _ => {⟨f,.leaf f hp⟩}
  | .split sp l r _ => closedLeaves ⟨_,l⟩ + closedLeaves ⟨_,r⟩

def TreeTransition.visited {V W : Multiset (TreeOccurrence L)} : TreeTransition V W → Multiset (TreeOccurrence L)
  | .leaf f hp _ _ => {⟨f,.leaf f hp⟩}
  | .split sp l r _ => {⟨_,.split sp l r⟩} + closedNodes ⟨_,l⟩ + closedNodes ⟨_,r⟩

def TreeTransition.step {V W : Multiset (TreeOccurrence L)} : (e : TreeTransition V W) → TreeStep W V
  | .leaf f hp hn rest => .leaf f hp hn rest
  | .split sp l r rest => .split sp l r rest

theorem TreeTransition.focus_mem {V W : Multiset (TreeOccurrence L)} (e : TreeTransition V W) : e.focus ∈ V := by
  cases e <;> exact Multiset.mem_cons_self _ _

theorem TreeTransition.exposed_stored {V W : Multiset (TreeOccurrence L)} (e : TreeTransition V W)
    (u : TreeOccurrence L) (hu : u ∈ e.exposed) : StoredSubtree u e.focus := by
  cases e with
  | leaf f hp hn rest =>
    have he := Multiset.mem_singleton.mp hu
    subst u
    exact .root _
  | split sp l r rest =>
    rcases Multiset.mem_add.mp hu with hl | hr
    · unfold closedLeaves at hl
      split_ifs at hl with hn
      · simp at hl
      · exact .left sp l r (leafOccurrences_stored l u hl)
    · unfold closedLeaves at hr
      split_ifs at hr with hn
      · simp at hr
      · exact .right sp l r (leafOccurrences_stored r u hr)

theorem TreeTransition.leaf_conservation {V W : Multiset (TreeOccurrence L)} (e : TreeTransition V W) :
    frontierLeaves V = frontierLeaves W + e.exposed := by
  cases e with
  | leaf f hp hn rest => simp [frontierLeaves,TreeTransition.exposed,leafOccurrences,add_comm]
  | split sp l r rest =>
    simp only [frontierLeaves,Multiset.cons_bind,Multiset.add_bind,leafOccurrences,TreeTransition.exposed]
    change (leafOccurrences l + leafOccurrences r) + frontierLeaves rest =
      (frontierLeaves (openTree ⟨_,l⟩) + frontierLeaves (openTree ⟨_,r⟩) + frontierLeaves rest) +
        (closedLeaves ⟨_,l⟩ + closedLeaves ⟨_,r⟩)
    rw [←open_closed_leaves ⟨_,l⟩,←open_closed_leaves ⟨_,r⟩]
    ac_rfl

theorem TreeTransition.node_conservation {V W : Multiset (TreeOccurrence L)} (e : TreeTransition V W) :
    frontierNodes V = frontierNodes W + e.visited := by
  cases e with
  | leaf f hp hn rest => simp [frontierNodes,TreeTransition.visited,nodeOccurrences,add_comm]
  | split sp l r rest =>
    simp only [frontierNodes,Multiset.cons_bind,Multiset.add_bind,nodeOccurrences,TreeTransition.visited]
    change ({⟨_,.split sp l r⟩} + nodeOccurrences l + nodeOccurrences r) + frontierNodes rest =
      (frontierNodes (openTree ⟨_,l⟩) + frontierNodes (openTree ⟨_,r⟩) + frontierNodes rest) +
        ({⟨_,.split sp l r⟩} + closedNodes ⟨_,l⟩ + closedNodes ⟨_,r⟩)
    rw [←open_closed_nodes ⟨_,l⟩,←open_closed_nodes ⟨_,r⟩]
    ac_rfl

theorem treeTransition_exists (V : Multiset (TreeOccurrence L)) (valid : OpenFrontier V) (hne : V ≠ 0) :
    ∃ W, Nonempty (TreeTransition V W) := by
  obtain ⟨⟨f,t⟩,ht⟩ := Multiset.exists_mem_of_ne_zero hne
  have hn := valid ⟨f,t⟩ ht
  obtain ⟨rest,rfl⟩ := Multiset.exists_cons_of_mem ht
  cases t with
  | leaf f hp => exact ⟨rest,⟨.leaf f hp hn rest⟩⟩
  | split sp l r => exact ⟨_,⟨.split sp l r rest⟩⟩

def nextTree (V : Multiset (TreeOccurrence L)) (valid : OpenFrontier V) (hne : V ≠ 0) :
    Σ W, TreeTransition V W :=
  ⟨Classical.choose (treeTransition_exists V valid hne),
    Classical.choice (Classical.choose_spec (treeTransition_exists V valid hne))⟩

def TreeTransition.cast {V W V' W' : Multiset (TreeOccurrence L)}
    (hv : V = V') (hw : W = W') (e : TreeTransition V W) : TreeTransition V' W' := by
  cases hv
  cases hw
  exact e

theorem TreeTransition.cast_focus {V W V' W' : Multiset (TreeOccurrence L)}
    (hv : V = V') (hw : W = W') (e : TreeTransition V W) : (e.cast hv hw).focus = e.focus := by
  cases hv
  cases hw
  rfl

theorem TreeTransition.cast_exposed {V W V' W' : Multiset (TreeOccurrence L)}
    (hv : V = V') (hw : W = W') (e : TreeTransition V W) : (e.cast hv hw).exposed = e.exposed := by
  cases hv
  cases hw
  rfl

theorem TreeTransition.cast_visited {V W V' W' : Multiset (TreeOccurrence L)}
    (hv : V = V') (hw : W = W') (e : TreeTransition V W) : (e.cast hv hw).visited = e.visited := by
  cases hv
  cases hw
  rfl

variable {κ : Type*} [DecidableEq κ] {U : Finset κ}

def StoredFrontier (root : κ → TreeOccurrence L) (q : FrozenQueue L U) : Prop :=
  ∀ k t, t ∈ q.work k → StoredSubtree t (root k)

theorem initial_stored (root : κ → TreeOccurrence L) : StoredFrontier root (FrozenQueue.initial U root) := by
  intro k t ht
  change t ∈ openTree (root k) at ht
  unfold openTree at ht
  split_ifs at ht with hn
  · have he := Multiset.mem_singleton.mp ht
    subst t
    exact .root _
  · simp at ht

end Holant.LocalDrafts.RemoteWork.StableClosureV2.TokenExecution
