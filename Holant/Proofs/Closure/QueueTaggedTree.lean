import Holant.Proofs.Closure.QueueTaggedLookup
import Holant.Proofs.Closure.QueueExecution

/-! RECONSTRUCTED exact addressed stored-tree transitions and multiset ledgers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueTagged
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
variable {L : Type*} [Field L]
attribute [local instance] Classical.propDecidable

def treeLeaves {f : AnySignature L} (t : FactorTree f) (p : List Bool) : Multiset (Item L) :=
  match t with
  | .leaf f hp => {(p,⟨f,.leaf f hp⟩)}
  | .split sp l r => treeLeaves l (p++[false]) + treeLeaves r (p++[true])
abbrev taggedLeaves {f : AnySignature L} (t : FactorTree f) (p : List Bool) := treeLeaves t p

def treeNodes {f : AnySignature L} (t : FactorTree f) (p : List Bool) : Multiset (Item L) :=
  match t with
  | .leaf f hp => {(p,⟨f,.leaf f hp⟩)}
  | .split sp l r => {(p,⟨_,.split sp l r⟩)} + treeNodes l (p++[false]) + treeNodes r (p++[true])

theorem treeLeaves_project {f : AnySignature L} (t : FactorTree f) (p : List Bool) :
    (treeLeaves t p).map Prod.snd = leafOccurrences t := by
  induction t generalizing p with
  | leaf => rfl
  | split sp l r il ir => simp [treeLeaves,leafOccurrences,il,ir]

theorem treeNodes_project {f : AnySignature L} (t : FactorTree f) (p : List Bool) :
    (treeNodes t p).map Prod.snd = TokenExecution.nodeOccurrences t := by
  induction t generalizing p with
  | leaf => rfl
  | split sp l r il ir => simp [treeNodes,TokenExecution.nodeOccurrences,il,ir]

def openItem (u : Item L) : Multiset (Item L) := if 2 ≤ u.2.1.1 then {u} else 0
def closedLeaves (u : Item L) : Multiset (Item L) := if 2 ≤ u.2.1.1 then 0 else treeLeaves u.2.2 u.1
def closedNodes (u : Item L) : Multiset (Item L) := if 2 ≤ u.2.1.1 then 0 else treeNodes u.2.2 u.1
def frontierLeaves (W : Multiset (Item L)) : Multiset (Item L) := W.bind (fun u => treeLeaves u.2.2 u.1)
def frontierNodes (W : Multiset (Item L)) : Multiset (Item L) := W.bind (fun u => treeNodes u.2.2 u.1)

@[simp] theorem openItem_project (u : Item L) : (openItem u).map Prod.snd = openTree u.2 := by
  by_cases hn : 2 ≤ u.2.1.1 <;> simp [openItem,openTree,hn]

theorem closedLeaves_project (u : Item L) : (closedLeaves u).map Prod.snd = TokenExecution.closedLeaves u.2 := by
  by_cases hn : 2 ≤ u.2.1.1 <;> simp [closedLeaves,TokenExecution.closedLeaves,hn,treeLeaves_project]

theorem closedNodes_project (u : Item L) : (closedNodes u).map Prod.snd = TokenExecution.closedNodes u.2 := by
  by_cases hn : 2 ≤ u.2.1.1 <;> simp [closedNodes,TokenExecution.closedNodes,hn,treeNodes_project]

theorem open_closed_leaves (u : Item L) : frontierLeaves (openItem u) + closedLeaves u = treeLeaves u.2.2 u.1 := by
  by_cases hn : 2 ≤ u.2.1.1 <;> simp [openItem,closedLeaves,frontierLeaves,hn]

theorem open_closed_nodes (u : Item L) : frontierNodes (openItem u) + closedNodes u = treeNodes u.2.2 u.1 := by
  by_cases hn : 2 ≤ u.2.1.1 <;> simp [openItem,closedNodes,frontierNodes,hn]

theorem treeLeaves_located (root : TreeOccurrence L) (t : TreeOccurrence L) (p : List Bool)
    (located : lookupTree root p = some t) (u : Item L) (hu : u ∈ treeLeaves t.2 p) : lookupTree root u.1 = some u.2 := by
  obtain ⟨f,t⟩ := t
  induction t generalizing p with
  | leaf f hp =>
    have he := Multiset.mem_singleton.mp hu
    subst u
    exact located
  | split sp l r il ir =>
    rcases Multiset.mem_add.mp hu with hl | hr
    · apply il (p++[false]) ?_ hl
      rw [lookupTree_append_of_some root p [false] ⟨_,.split sp l r⟩ located]
      rfl
    · apply ir (p++[true]) ?_ hr
      rw [lookupTree_append_of_some root p [true] ⟨_,.split sp l r⟩ located]
      rfl

inductive TreeTransition : Multiset (Item L) → Multiset (Item L) → Type _
  | leaf (p : List Bool) (f : AnySignature L) (hp : Prime f) (hn : 2 ≤ f.1) (rest : Multiset (Item L)) :
      TreeTransition ((p,⟨f,.leaf f hp⟩) ::ₘ rest) rest
  | split {f a b : AnySignature L} (p : List Bool) (sp : ProperSplit f a b)
      (l : FactorTree a) (r : FactorTree b) (rest : Multiset (Item L)) :
      TreeTransition ((p,⟨f,.split sp l r⟩) ::ₘ rest)
        (openItem (p++[false],⟨a,l⟩) + openItem (p++[true],⟨b,r⟩) + rest)

def TreeTransition.focus {V W : Multiset (Item L)} : TreeTransition V W → Item L
  | .leaf p f hp _ _ => (p,⟨f,.leaf f hp⟩)
  | .split p sp l r _ => (p,⟨_,.split sp l r⟩)
def TreeTransition.exposed {V W : Multiset (Item L)} : TreeTransition V W → Multiset (Item L)
  | .leaf p f hp _ _ => {(p,⟨f,.leaf f hp⟩)}
  | .split p sp l r _ => closedLeaves (p++[false],⟨_,l⟩) + closedLeaves (p++[true],⟨_,r⟩)
def TreeTransition.visited {V W : Multiset (Item L)} : TreeTransition V W → Multiset (Item L)
  | .leaf p f hp _ _ => {(p,⟨f,.leaf f hp⟩)}
  | .split p sp l r _ => {(p,⟨_,.split sp l r⟩)} + closedNodes (p++[false],⟨_,l⟩) + closedNodes (p++[true],⟨_,r⟩)
def TreeTransition.children {V W : Multiset (Item L)} : TreeTransition V W → Multiset (Item L)
  | .leaf _ _ _ _ _ => 0
  | .split p sp l r _ => {(p++[false],⟨_,l⟩)} + {(p++[true],⟨_,r⟩)}

theorem TreeTransition.focus_mem {V W : Multiset (Item L)} (e : TreeTransition V W) : e.focus ∈ V := by
  cases e <;> exact Multiset.mem_cons_self _ _

def TreeTransition.projected {V W : Multiset (Item L)} (e : TreeTransition V W) :
    TokenExecution.TreeTransition (V.map Prod.snd) (W.map Prod.snd) := by
  cases e with
  | leaf p f hp hn =>
    exact (TokenExecution.TreeTransition.leaf f hp hn (W.map Prod.snd)).cast (by simp) rfl
  | split p sp l r rest =>
    exact (TokenExecution.TreeTransition.split sp l r (rest.map Prod.snd)).cast (by simp)
      (by simp only [Multiset.map_add,openItem_project])

theorem TreeTransition.projected_focus {V W : Multiset (Item L)} (e : TreeTransition V W) : e.projected.focus = e.focus.2 := by
  cases e <;> unfold TreeTransition.projected <;> rw [TokenExecution.TreeTransition.cast_focus] <;> rfl

theorem TreeTransition.exposed_project {V W : Multiset (Item L)} (e : TreeTransition V W) :
    e.exposed.map Prod.snd = e.projected.exposed := by
  cases e <;> unfold TreeTransition.projected <;> rw [TokenExecution.TreeTransition.cast_exposed] <;>
    simp [TreeTransition.exposed,TokenExecution.TreeTransition.exposed,closedLeaves_project]

theorem TreeTransition.visited_project {V W : Multiset (Item L)} (e : TreeTransition V W) :
    e.visited.map Prod.snd = e.projected.visited := by
  cases e <;> unfold TreeTransition.projected <;> rw [TokenExecution.TreeTransition.cast_visited] <;>
    simp [TreeTransition.visited,TokenExecution.TreeTransition.visited,closedNodes_project]

theorem TreeTransition.children_located {V W : Multiset (Item L)} (e : TreeTransition V W)
    (root : TreeOccurrence L) (hf : lookupTree root e.focus.1 = some e.focus.2)
    (u : Item L) (hu : u ∈ e.children) : lookupTree root u.1 = some u.2 := by
  cases e with
  | leaf => simp [TreeTransition.children] at hu
  | split p sp l r rest =>
    rcases Multiset.mem_add.mp hu with hl | hr
    · have he := Multiset.mem_singleton.mp hl
      subst u
      rw [lookupTree_append_of_some root p [false] ⟨_,.split sp l r⟩ hf]
      rfl
    · have he := Multiset.mem_singleton.mp hr
      subst u
      rw [lookupTree_append_of_some root p [true] ⟨_,.split sp l r⟩ hf]
      rfl

theorem TreeTransition.exposed_located {V W : Multiset (Item L)} (e : TreeTransition V W)
    (root : TreeOccurrence L) (hf : lookupTree root e.focus.1 = some e.focus.2)
    (u : Item L) (hu : u ∈ e.exposed) : lookupTree root u.1 = some u.2 := by
  cases e with
  | leaf p f hp hn rest =>
    have he := Multiset.mem_singleton.mp hu
    subst u
    exact hf
  | split p sp l r rest =>
    rcases Multiset.mem_add.mp hu with hl | hr
    · unfold closedLeaves at hl
      split_ifs at hl with hn
      · simp at hl
      · apply treeLeaves_located root ⟨_,l⟩ (p++[false]) ?_ u hl
        rw [lookupTree_append_of_some root p [false] ⟨_,.split sp l r⟩ hf]
        rfl
    · unfold closedLeaves at hr
      split_ifs at hr with hn
      · simp at hr
      · apply treeLeaves_located root ⟨_,r⟩ (p++[true]) ?_ u hr
        rw [lookupTree_append_of_some root p [true] ⟨_,.split sp l r⟩ hf]
        rfl

theorem TreeTransition.leaf_conservation {V W : Multiset (Item L)} (e : TreeTransition V W) :
    frontierLeaves V = frontierLeaves W + e.exposed := by
  cases e with
  | leaf => simp [frontierLeaves,treeLeaves,TreeTransition.exposed,add_comm]
  | split p sp l r rest =>
    simp only [frontierLeaves,Multiset.cons_bind,Multiset.add_bind,treeLeaves,TreeTransition.exposed]
    rw [←open_closed_leaves (p++[false],⟨_,l⟩),←open_closed_leaves (p++[true],⟨_,r⟩)]
    unfold frontierLeaves
    ac_rfl

theorem TreeTransition.node_conservation {V W : Multiset (Item L)} (e : TreeTransition V W) :
    frontierNodes V = frontierNodes W + e.visited := by
  cases e with
  | leaf => simp [frontierNodes,treeNodes,TreeTransition.visited,add_comm]
  | split p sp l r rest =>
    simp only [frontierNodes,Multiset.cons_bind,Multiset.add_bind,treeNodes,TreeTransition.visited]
    rw [←open_closed_nodes (p++[false],⟨_,l⟩),←open_closed_nodes (p++[true],⟨_,r⟩)]
    unfold frontierNodes
    ac_rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueTagged
