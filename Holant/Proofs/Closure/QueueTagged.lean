import Holant.Proofs.Closure.QueueTaggedState

/-! RECONSTRUCTED executable addressed queue. Its ordinary trace is literally
its projection. The counted path ledgers cover every exact saved occurrence. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueTagged
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
variable {L : Type*} [Field L] {κ : Type*} [DecidableEq κ] {U : Finset κ}
attribute [local instance] Classical.propDecidable
variable {root : κ → TreeOccurrence L}

inductive Trace : State (U:=U) root → State (U:=U) root → Type _
  | nil (S : State (U:=U) root) : Trace S S
  | cons {S T R : State (U:=U) root} (event : Transition S T) (rest : Trace T R) : Trace S R

def Trace.projected {S T : State (U:=U) root} : Trace S T → TokenExecution.Trace S.queue T.queue
  | .nil S => .nil S.queue
  | .cons e rest => .cons e.projected rest.projected

def Trace.exposed {S T : State (U:=U) root} (h : Trace S T) (k : κ) : Multiset (Item L) :=
  match h with
  | .nil _ => 0
  | .cons e rest => e.exposedAt k + rest.exposed k

def Trace.visited {S T : State (U:=U) root} (h : Trace S T) (k : κ) : Multiset (Item L) :=
  match h with
  | .nil _ => 0
  | .cons e rest => e.visitedAt k + rest.visited k

theorem Trace.exposed_project {S T : State (U:=U) root} (h : Trace S T) (k : κ) :
    (h.exposed k).map Prod.snd = h.projected.exposed k := by
  induction h with
  | nil => rfl
  | cons e rest ih => simp only [Trace.exposed,Trace.projected,Multiset.map_add,
      TokenExecution.Trace.exposed,e.exposed_project,ih]

theorem Trace.visited_project {S T : State (U:=U) root} (h : Trace S T) (k : κ) :
    (h.visited k).map Prod.snd = h.projected.visited k := by
  induction h with
  | nil => rfl
  | cons e rest ih => simp only [Trace.visited,Trace.projected,Multiset.map_add,
      TokenExecution.Trace.visited,e.visited_project,ih]

theorem Trace.leaf_conservation {S T : State (U:=U) root} (h : Trace S T) (k : κ) :
    frontierLeaves (S.work k) = frontierLeaves (T.work k) + h.exposed k := by
  induction h with
  | nil => simp [Trace.exposed]
  | cons e rest ih =>
    rw [e.leaf_conservation,ih]
    simp only [Trace.exposed]
    ac_rfl

theorem Trace.node_conservation {S T : State (U:=U) root} (h : Trace S T) (k : κ) :
    frontierNodes (S.work k) = frontierNodes (T.work k) + h.visited k := by
  induction h with
  | nil => simp [Trace.visited]
  | cons e rest ih =>
    rw [e.node_conservation,ih]
    simp only [Trace.visited]
    ac_rfl

inductive EventIn : {S T A B : State (U:=U) root} → Trace S T → Transition A B → Prop
  | head {S T R : State (U:=U) root} (e : Transition S T) (rest : Trace T R) : EventIn (.cons e rest) e
  | tail {S T R A B : State (U:=U) root} (e : Transition S T) (rest : Trace T R)
      (actual : Transition A B) (recorded : EventIn rest actual) : EventIn (.cons e rest) actual

theorem Trace.exposed_event {S T : State (U:=U) root} (h : Trace S T) (k : κ)
    (u : Item L) (hu : u ∈ h.exposed k) :
    ∃ (A B : State (U:=U) root) (e : Transition A B), EventIn h e ∧ u ∈ e.exposedAt k := by
  induction h with
  | nil => simp [Trace.exposed] at hu
  | cons e rest ih =>
    rcases Multiset.mem_add.mp hu with he | hr
    · exact ⟨_,_,e,.head e rest,he⟩
    · obtain ⟨A,B,actual,hi,he⟩ := ih hr
      exact ⟨A,B,actual,.tail e rest actual hi,he⟩

theorem Trace.visited_event {S T : State (U:=U) root} (h : Trace S T) (k : κ)
    (u : Item L) (hu : u ∈ h.visited k) :
    ∃ (A B : State (U:=U) root) (e : Transition A B), EventIn h e ∧ u ∈ e.visitedAt k := by
  induction h with
  | nil => simp [Trace.visited] at hu
  | cons e rest ih =>
    rcases Multiset.mem_add.mp hu with he | hr
    · exact ⟨_,_,e,.head e rest,he⟩
    · obtain ⟨A,B,actual,hi,he⟩ := ih hr
      exact ⟨A,B,actual,.tail e rest actual hi,he⟩

structure Exhaustion (S : State (U:=U) root) where
  finalState : State (U:=U) root
  trace : Trace S finalState
  exhausted : finalState.queue.todo = ∅

theorem treeTransition_exists (V : Multiset (Item L))
    (valid : ∀ u ∈ V, 2 ≤ u.2.1.1) (hne : V ≠ 0) : ∃ W, Nonempty (TreeTransition V W) := by
  obtain ⟨⟨p,⟨f,t⟩⟩,ht⟩ := Multiset.exists_mem_of_ne_zero hne
  have hn := valid (p,⟨f,t⟩) ht
  obtain ⟨rest,rfl⟩ := Multiset.exists_cons_of_mem ht
  cases t with
  | leaf f hp => exact ⟨rest,⟨.leaf p f hp hn rest⟩⟩
  | split sp l r => exact ⟨_,⟨.split p sp l r rest⟩⟩

def nextTree (V : Multiset (Item L)) (valid : ∀ u ∈ V, 2 ≤ u.2.1.1) (hne : V ≠ 0) : Σ W, TreeTransition V W :=
  ⟨Classical.choose (treeTransition_exists V valid hne),
    Classical.choice (Classical.choose_spec (treeTransition_exists V valid hne))⟩

def next (S : State (U:=U) root) (nonempty : S.queue.todo.Nonempty) : Σ T, Transition S T := by
  let k := Classical.choose nonempty
  have hk : k ∈ S.queue.todo := Classical.choose_spec nonempty
  by_cases hz : S.work k = 0
  · exact ⟨S.finish k hk hz,.finish S k hk hz⟩
  · have hv : ∀ u ∈ S.work k, 2 ≤ u.2.1.1 := by
      intro u hu
      apply S.valid k hk u.2
      rw [S.project]
      exact Multiset.mem_map.mpr ⟨u,hu,rfl⟩
    let e := nextTree (S.work k) hv hz
    exact ⟨S.process k hk e.1 e.2,.process S k hk e.1 e.2⟩

theorem projected_wellFounded : WellFounded (fun T S : State (U:=U) root => FrozenQueue.Step T.queue S.queue) :=
  InvImage.wf State.queue FrozenQueue.step_wellFounded

def exhaust (S : State (U:=U) root) : Exhaustion S :=
  projected_wellFounded.fix (C:=fun S => Exhaustion S) (fun S recurse =>
    if hn : S.queue.todo.Nonempty then
      let e := next S hn
      let r := recurse e.1 e.2.projected.step
      ⟨r.finalState,.cons e.2 r.trace,r.exhausted⟩
    else ⟨S,.nil S,Finset.not_nonempty_iff_eq_empty.mp hn⟩) S

def initialExhaustion (root : κ → TreeOccurrence L) : Exhaustion (State.initial (U:=U) root) := exhaust _

def projectedExhaustion (root : κ → TreeOccurrence L) : TokenExecution.Exhaustion (FrozenQueue.initial U root) :=
  ⟨(initialExhaustion (U:=U) root).finalState.queue,(initialExhaustion (U:=U) root).trace.projected,
    (initialExhaustion (U:=U) root).exhausted⟩

def initialExposed (root : κ → TreeOccurrence L) (k : κ) : Multiset (Item L) :=
  closedLeaves ([],root k) + (initialExhaustion (U:=U) root).trace.exposed k

def initialVisited (root : κ → TreeOccurrence L) (k : κ) : Multiset (Item L) :=
  closedNodes ([],root k) + (initialExhaustion (U:=U) root).trace.visited k

theorem initial_leaf_addresses (root : κ → TreeOccurrence L) (k : κ) (hk : k ∈ U) :
    initialExposed (U:=U) root k = treeLeaves (root k).2 [] := by
  let E := initialExhaustion (U:=U) root
  have hf : E.finalState.work k = 0 := E.finalState.completed k hk (by rw [E.exhausted]; simp)
  have hc := E.trace.leaf_conservation k
  rw [hf] at hc
  simp only [frontierLeaves,Multiset.zero_bind,zero_add] at hc
  change frontierLeaves (openItem ([],root k)) = E.trace.exposed k at hc
  change closedLeaves ([],root k) + E.trace.exposed k = _
  rw [←hc,add_comm,open_closed_leaves]

theorem initial_node_addresses (root : κ → TreeOccurrence L) (k : κ) (hk : k ∈ U) :
    initialVisited (U:=U) root k = treeNodes (root k).2 [] := by
  let E := initialExhaustion (U:=U) root
  have hf : E.finalState.work k = 0 := E.finalState.completed k hk (by rw [E.exhausted]; simp)
  have hc := E.trace.node_conservation k
  rw [hf] at hc
  simp only [frontierNodes,Multiset.zero_bind,zero_add] at hc
  change frontierNodes (openItem ([],root k)) = E.trace.visited k at hc
  change closedNodes ([],root k) + E.trace.visited k = _
  rw [←hc,add_comm,open_closed_nodes]

theorem initialExposed_project (root : κ → TreeOccurrence L) (k : κ) :
    (initialExposed (U:=U) root k).map Prod.snd = TokenExecution.closedLeaves (root k) +
      (projectedExhaustion (U:=U) root).trace.exposed k := by
  simp only [initialExposed,Multiset.map_add,closedLeaves_project,Trace.exposed_project,projectedExhaustion]
  rfl

theorem initialVisited_project (root : κ → TreeOccurrence L) (k : κ) :
    (initialVisited (U:=U) root k).map Prod.snd = TokenExecution.closedNodes (root k) +
      (projectedExhaustion (U:=U) root).trace.visited k := by
  simp only [initialVisited,Multiset.map_add,closedNodes_project,Trace.visited_project,projectedExhaustion]
  rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueTagged
