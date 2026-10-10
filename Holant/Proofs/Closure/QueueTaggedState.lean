import Holant.Proofs.Closure.QueueTaggedTree

/-! RECONSTRUCTED addressed states, with exact frozen projection, constructor
location, and a completed-work invariant. No stored tree is selected again. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueTagged
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
variable {L : Type*} [Field L] {κ : Type*} [DecidableEq κ] {U : Finset κ}
attribute [local instance] Classical.propDecidable

theorem openItem_mem {v u : Item L} (h : u ∈ openItem v) : u = v := by
  unfold openItem at h
  split_ifs at h with hn
  · exact Multiset.mem_singleton.mp h
  · simp at h

theorem TreeTransition.after_located {V W : Multiset (Item L)} (e : TreeTransition V W)
    (root : TreeOccurrence L) (h : ∀ u ∈ V, lookupTree root u.1 = some u.2) :
    ∀ u ∈ W, lookupTree root u.1 = some u.2 := by
  have hf := h e.focus e.focus_mem
  cases e with
  | leaf p f hp hn =>
    intro u hu
    exact h u (Multiset.mem_cons_of_mem hu)
  | split p sp l r rest =>
    intro u hu
    rcases Multiset.mem_add.mp hu with hl | hr
    · rcases Multiset.mem_add.mp hl with hl | hr
      · have he := openItem_mem hl
        subst u
        rw [lookupTree_append_of_some root p [false] ⟨_,.split sp l r⟩ hf]
        rfl
      · have he := openItem_mem hr
        subst u
        rw [lookupTree_append_of_some root p [true] ⟨_,.split sp l r⟩ hf]
        rfl
    · exact h u (Multiset.mem_cons_of_mem hr)

structure State (root : κ → TreeOccurrence L) where
  queue : FrozenQueue L U
  work : κ → Multiset (Item L)
  project : ∀ k, queue.work k = (work k).map Prod.snd
  located : ∀ k u, u ∈ work k → lookupTree (root k) u.1 = some u.2
  valid : queue.Valid
  completed : ∀ k ∈ U, k ∉ queue.todo → work k = 0

variable {root : κ → TreeOccurrence L}

def State.initial (root : κ → TreeOccurrence L) : State (U:=U) root := by
  refine ⟨FrozenQueue.initial U root,(fun k => openItem ([],root k)),?_,?_,FrozenQueue.initial_valid U root,?_⟩
  · intro k
    exact (openItem_project ([],root k)).symm
  · intro k u hu
    have he := openItem_mem hu
    subst u
    rfl
  · intro k hk hn
    exact (hn hk).elim

def State.inspection (S : State (U:=U) root) (k : κ) (W : Multiset (Item L))
    (e : TreeTransition (S.work k) W) : TokenExecution.TreeTransition (S.queue.work k) (W.map Prod.snd) :=
  e.projected.cast (S.project k).symm rfl

theorem State.inspection_focus (S : State (U:=U) root) (k : κ) (W : Multiset (Item L))
    (e : TreeTransition (S.work k) W) : (S.inspection k W e).focus = e.focus.2 := by
  unfold State.inspection
  rw [TokenExecution.TreeTransition.cast_focus,e.projected_focus]

theorem State.storedFrontier (S : State (U:=U) root) : TokenExecution.StoredFrontier root S.queue := by
  intro k t ht
  rw [S.project] at ht
  obtain ⟨u,hu,rfl⟩ := Multiset.mem_map.mp ht
  exact lookupTree_stored _ _ _ (S.located k u hu)

def State.finish (S : State (U:=U) root) (k : κ) (hk : k ∈ S.queue.todo) (hz : S.work k = 0) : State (U:=U) root := by
  refine ⟨S.queue.finish k,S.work,S.project,S.located,?_,?_⟩
  · exact FrozenQueue.step_valid (.finish S.queue k hk (by rw [S.project,hz]; rfl)) S.valid
  · intro j hj hn
    by_cases he : j = k
    · subst j
      exact hz
    · exact S.completed j hj (fun ht => hn (Finset.mem_erase.mpr ⟨he,ht⟩))

def State.process (S : State (U:=U) root) (k : κ) (hk : k ∈ S.queue.todo)
    (W : Multiset (Item L)) (e : TreeTransition (S.work k) W) : State (U:=U) root := by
  refine ⟨S.queue.process k (W.map Prod.snd),Function.update S.work k W,?_,?_,?_,?_⟩
  · intro j
    by_cases he : j = k
    · subst j
      simp [FrozenQueue.process,Function.update_self]
    · simp [FrozenQueue.process,Function.update_of_ne he,S.project]
  · intro j u hu
    by_cases he : j = k
    · subst j
      rw [Function.update_self] at hu
      exact e.after_located (root k) (S.located k) u hu
    · rw [Function.update_of_ne he] at hu
      exact S.located j u hu
  · exact FrozenQueue.step_valid (.process S.queue k hk _ (S.inspection k W e).step) S.valid
  · intro j hj hn
    have he : j ≠ k := by intro he; subst j; exact hn hk
    rw [Function.update_of_ne he]
    exact S.completed j hj hn

inductive Transition : State (U:=U) root → State (U:=U) root → Type _
  | finish (S : State (U:=U) root) (k : κ) (pending : k ∈ S.queue.todo) (empty : S.work k = 0) :
      Transition S (S.finish k pending empty)
  | process (S : State (U:=U) root) (k : κ) (pending : k ∈ S.queue.todo)
      (W : Multiset (Item L)) (tree : TreeTransition (S.work k) W) : Transition S (S.process k pending W tree)

def Transition.projected {S T : State (U:=U) root} (e : Transition S T) : TokenExecution.Transition S.queue T.queue := by
  cases e with
  | finish k hk hz => exact .finish S.queue k hk (by rw [S.project,hz]; rfl)
  | process k hk W tree => exact .process S.queue k hk _ (S.inspection k W tree)

def Transition.exposedAt {S T : State (U:=U) root} (e : Transition S T) (j : κ) : Multiset (Item L) :=
  match e with
  | .finish _ _ _ _ => 0
  | .process _ k _ _ tree => if j = k then tree.exposed else 0

def Transition.visitedAt {S T : State (U:=U) root} (e : Transition S T) (j : κ) : Multiset (Item L) :=
  match e with
  | .finish _ _ _ _ => 0
  | .process _ k _ _ tree => if j = k then tree.visited else 0

theorem Transition.leaf_conservation {S T : State (U:=U) root} (e : Transition S T) (j : κ) :
    frontierLeaves (S.work j) = frontierLeaves (T.work j) + e.exposedAt j := by
  cases e with
  | finish => simp [State.finish,Transition.exposedAt]
  | process k hk W tree =>
    by_cases he : j = k
    · subst j
      simpa [State.process,Transition.exposedAt] using tree.leaf_conservation
    · simp [State.process,Transition.exposedAt,he]

theorem Transition.node_conservation {S T : State (U:=U) root} (e : Transition S T) (j : κ) :
    frontierNodes (S.work j) = frontierNodes (T.work j) + e.visitedAt j := by
  cases e with
  | finish => simp [State.finish,Transition.visitedAt]
  | process k hk W tree =>
    by_cases he : j = k
    · subst j
      simpa [State.process,Transition.visitedAt] using tree.node_conservation
    · simp [State.process,Transition.visitedAt,he]

theorem Transition.exposed_project {S T : State (U:=U) root} (e : Transition S T) (j : κ) :
    (e.exposedAt j).map Prod.snd = e.projected.exposedAt j := by
  cases e with
  | finish => rfl
  | process k hk W tree =>
    by_cases he : j = k
    · subst j
      simp only [Transition.exposedAt,if_pos rfl,Transition.projected,TokenExecution.Transition.exposedAt]
      unfold State.inspection
      rw [TokenExecution.TreeTransition.cast_exposed]
      exact tree.exposed_project
    · simp [Transition.exposedAt,TokenExecution.Transition.exposedAt,Transition.projected,he]

theorem Transition.visited_project {S T : State (U:=U) root} (e : Transition S T) (j : κ) :
    (e.visitedAt j).map Prod.snd = e.projected.visitedAt j := by
  cases e with
  | finish => rfl
  | process k hk W tree =>
    by_cases he : j = k
    · subst j
      simp only [Transition.visitedAt,if_pos rfl,Transition.projected,TokenExecution.Transition.visitedAt]
      unfold State.inspection
      rw [TokenExecution.TreeTransition.cast_visited]
      exact tree.visited_project
    · simp [Transition.visitedAt,TokenExecution.Transition.visitedAt,Transition.projected,he]

end Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueTagged
