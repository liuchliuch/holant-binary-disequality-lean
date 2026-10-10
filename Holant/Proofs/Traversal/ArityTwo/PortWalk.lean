import Holant.Proofs.Traversal.ArityTwo.Transfer
import Holant.Complexity.GraphPreprocessing.ComponentSelection.RawRoots


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
open Holant Holant.Complexity Holant.OneHot.Computable
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

abbrev degree (v : Fin r.vertices.length) := arity (r.vertices.get v).1

/-- Cross an actual edge, including an edge whose endpoint vertices coincide. -/
def cross (p : r.Ports arity) : r.Ports arity :=
  let q := r.route h p
  r.lookup h (q.1,!q.2)

@[simp] theorem route_cross (p : r.Ports arity) :
    r.route h (cross r h p) = ((r.route h p).1,!(r.route h p).2) := r.route_lookup h _

@[simp] theorem cross_cross (p : r.Ports arity) : cross r h (cross r h p) = p := by
  apply (r.route_bijective h).1
  simp

theorem cross_ne (p : r.Ports arity) : cross r h p ≠ p := by
  intro heq
  have hh := congrArg (fun p => (r.route h p).2) heq
  rw [route_cross] at hh
  cases (r.route h p).2 <;> simp at hh

theorem cross_injective : Function.Injective (cross r h) := by
  intro p q hpq
  simpa only [cross_cross] using congrArg (cross r h) hpq

/-- Only binary vertices have a continuation through a different local port. -/
def other (p : r.Ports arity) : Option (r.Ports arity) :=
  if hd : degree (arity := arity) r p.1 = 2 then
    some ⟨p.1,⟨1-p.2.val,by
      change 1-p.2.val < degree (arity := arity) r p.1
      rw [hd]
      omega⟩⟩
  else none

@[simp] theorem other_none_iff (p : r.Ports arity) :
    other r p = none ↔ degree (arity := arity) r p.1 ≠ 2 := by
  unfold other
  split <;> simp_all

theorem other_some (p q : r.Ports arity) (hq : other r p = some q) :
    q.1 = p.1 ∧ q.2.val = 1-p.2.val ∧ degree (arity := arity) r p.1 = 2 := by
  unfold other at hq
  split at hq
  · cases hq
    exact ⟨rfl,rfl,‹_›⟩
  · contradiction

theorem terminal_unary (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : other r p = none) : degree (arity := arity) r p.1 = 1 := by
  have hi := p.2.isLt
  have hb := hd p.1
  have hn := (other_none_iff r p).mp hp
  change p.2.val < degree (arity := arity) r p.1 at hi
  omega

theorem same_unary_vertex (p q : r.Ports arity) (hp : degree (arity := arity) r p.1 = 1)
    (hv : q.1 = p.1) : q = p := by
  rcases p with ⟨v,i⟩
  rcases q with ⟨w,j⟩
  dsimp only at hv hp
  subst w
  have hij : j = i := by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    change arity (r.vertices.get v).1 = 1 at hp
    omega
  cases hij
  rfl

/-- A closed unary occurrence cannot be an isolated self-loop component. -/
theorem unary_cross_vertex_ne (p : r.Ports arity) (hp : degree (arity := arity) r p.1 = 1) :
    (cross r h p).1 ≠ p.1 := by
  intro hv
  exact cross_ne r h p (same_unary_vertex r p (cross r h p) hp hv)

/-- A nullary occurrence has no incident endpoint at all. -/
theorem nullary_no_port (v : Fin r.vertices.length) (hv : degree (arity := arity) r v = 0)
    (p : r.Ports arity) : p.1 ≠ v := by
  intro hp
  have hi := p.2.isLt
  change p.2.val < degree (arity := arity) r p.1 at hi
  have hz : degree (arity := arity) r p.1 = 0 := hp ▸ hv
  rw [hz] at hi
  omega

/-- Under the actual arity bound, a self-loop necessarily consumes a binary
occurrence, with two distinct original local ports. -/
theorem self_loop_binary (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hv : (cross r h p).1 = p.1) : degree (arity := arity) r p.1 = 2 := by
  have hi := p.2.isLt
  change p.2.val < degree (arity := arity) r p.1 at hi
  have hb := hd p.1
  have hn : degree (arity := arity) r p.1 ≠ 1 := fun hp => unary_cross_vertex_ne r h p hp hv
  omega

inductive Stop (P : Type*) where
  | terminal (p : P)
  | repeated (p : P)
  | exhausted
  deriving DecidableEq

/-- The seen-list contains original port occurrences, not just vertex IDs. -/
def walk : ℕ → List (r.Ports arity) → r.Ports arity → List (r.Ports arity) × Stop (r.Ports arity)
  | 0, _, _ => ([],.exhausted)
  | fuel+1, seen, p =>
      if p ∈ seen then ([],.repeated p)
      else match other r p with
        | none => ([p],.terminal p)
        | some q =>
          let tail := walk fuel (p::seen) (cross r h q)
          (p::tail.1,tail.2)

theorem walk_length (fuel : ℕ) (seen : List (r.Ports arity)) (p : r.Ports arity) :
    (walk r h fuel seen p).1.length ≤ fuel := by
  induction fuel generalizing seen p with
  | zero => simp [walk]
  | succ fuel ih =>
    simp only [walk]
    split
    · simp
    · split
      · simp
      · simpa only [List.length_cons] using Nat.succ_le_succ (ih _ _)

theorem walk_fresh (fuel : ℕ) (seen : List (r.Ports arity)) (p : r.Ports arity) :
    ∀ q ∈ (walk r h fuel seen p).1, q ∉ seen := by
  induction fuel generalizing seen p with
  | zero => simp [walk]
  | succ fuel ih =>
    simp only [walk]
    split
    · simp
    · rename_i hp
      split
      · simpa using hp
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · have hh := ih (p::seen) _ q hq
          exact fun hseen => hh (List.mem_cons_of_mem p hseen)

theorem walk_nodup (fuel : ℕ) (seen : List (r.Ports arity)) (p : r.Ports arity) :
    (walk r h fuel seen p).1.Nodup := by
  induction fuel generalizing seen p with
  | zero => simp [walk]
  | succ fuel ih =>
    simp only [walk]
    split
    · simp
    · split
      · simp
      · apply List.nodup_cons.mpr
        refine ⟨?_,ih _ _⟩
        intro hp
        exact walk_fresh r h fuel (p::seen) _ p hp (by simp)

/-- A terminal result really has no binary continuation. -/
theorem walk_terminal (fuel : ℕ) (seen : List (r.Ports arity)) (p q : r.Ports arity)
    (hq : (walk r h fuel seen p).2 = .terminal q) : other r q = none := by
  induction fuel generalizing seen p with
  | zero => simp [walk] at hq
  | succ fuel ih =>
    simp only [walk] at hq
    split at hq
    · contradiction
    · split at hq
      · cases hq
        assumption
      · exact ih _ _ hq

theorem walk_exhausted_length (fuel : ℕ) (seen : List (r.Ports arity)) (p : r.Ports arity)
    (he : (walk r h fuel seen p).2 = .exhausted) :
    (walk r h fuel seen p).1.length = fuel := by
  induction fuel generalizing seen p with
  | zero => rfl
  | succ fuel ih =>
    simp only [walk] at he ⊢
    split at he <;> simp_all only
    · contradiction
    · split at he <;> simp_all only
      · contradiction
      · simpa only [List.length_cons, ↓reduceIte] using congrArg Nat.succ (ih _ _ he)

/-- This is a derived finite termination bound, not an assumed successful walk.
It counts ports, so a self-loop's two ends are still separate occurrences. -/
theorem walk_not_exhausted (seen : List (r.Ports arity)) (p : r.Ports arity) :
    (walk r h (2*r.edges.length+1) seen p).2 ≠ .exhausted := by
  intro he
  have hlen := walk_exhausted_length r h _ seen p he
  have hn := walk_nodup r h (2*r.edges.length+1) seen p
  have hcard : (walk r h (2*r.edges.length+1) seen p).1.length ≤
      Fintype.card (r.Ports arity) := by
    rw [← List.toFinset_card_of_nodup hn]
    exact Finset.card_le_univ _
  have hp := r.ports_card_eq h
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hp
  omega

theorem walk_head (fuel : ℕ) (seen : List (r.Ports arity)) (p q : r.Ports arity)
    (qs : List (r.Ports arity)) (he : (walk r h fuel seen p).1 = q::qs) : q = p := by
  cases fuel with
  | zero => simp [walk] at he
  | succ fuel =>
    simp only [walk] at he
    split at he
    · contradiction
    · split at he <;> exact (List.cons.inj he).1.symm

/-- Adjacent entries use the unique other local port and the actual edge
involution. There is no adjacency assumption supplied with the output list. -/
def Follows : List (r.Ports arity) → Prop
  | [] => True
  | [_] => True
  | p::q::ps => (∃ out, other r p = some out ∧ cross r h out = q) ∧ Follows (q::ps)

theorem walk_follows (fuel : ℕ) (seen : List (r.Ports arity)) (p : r.Ports arity) :
    Follows r h (walk r h fuel seen p).1 := by
  induction fuel generalizing seen p with
  | zero => trivial
  | succ fuel ih =>
    simp only [walk]
    split
    · trivial
    · split
      · trivial
      · rename_i out ho
        have hi := ih (p::seen) (cross r h out)
        cases ht : (walk r h fuel (p::seen) (cross r h out)).1 with
        | nil => trivial
        | cons q qs =>
          have hh := walk_head r h fuel (p::seen) (cross r h out) q qs ht
          exact ⟨⟨out,ho,hh.symm⟩,by simpa only [ht] using hi⟩

theorem walk_repeated_mem (fuel : ℕ) (seen : List (r.Ports arity)) (p q : r.Ports arity)
    (he : (walk r h fuel seen p).2 = .repeated q) :
    q ∈ seen ∨ q ∈ (walk r h fuel seen p).1 := by
  induction fuel generalizing seen p with
  | zero => simp [walk] at he
  | succ fuel ih =>
    simp only [walk] at he ⊢
    split at he <;> simp_all only
    · cases he
      exact Or.inl ‹_›
    · split at he <;> simp_all only
      · contradiction
      · rcases ih _ _ he with hm | hm
        · rcases List.mem_cons.mp hm with rfl | hm
          · exact Or.inr (by simp)
          · exact Or.inl hm
        · exact Or.inr (List.mem_cons_of_mem _ hm)

/-- A genuine raw-input machine already supplies precisely these component IDs. -/
abbrev rootsMachine := GraphPreprocessing.ComponentSelection.RawRoots.machine

noncomputable def roots_timed :
    Turing.TM2OutputsInTime rootsMachine.computer (RawClosedNetwork.encoding.encode r)
      (some (GraphPreprocessing.ComponentSelection.RawRoots.outputEncoding.encode
        ((r.graph h).roots.map Fin.val)))
      ((GraphPreprocessing.ComponentSelection.RawRoots.timePolynomial s b arity).eval
        (RawClosedNetwork.encoding.encode r).length) :=
  GraphPreprocessing.ComponentSelection.RawRoots.timed ⟨r,h⟩

theorem original_vertex_partition (v : Fin r.vertices.length) :
    ∃! root : Fin r.vertices.length,
      root ∈ (r.graph h).roots ∧ v ∈ (r.graph h).componentVertices root :=
  (r.graph h).unique_vertex_component v

theorem original_edge_partition (e : (r.graph h).Edge) :
    ∃! root : Fin r.vertices.length,
      root ∈ (r.graph h).roots ∧ e ∈ (r.graph h).componentEdges root :=
  (r.graph h).unique_edge_component e

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
