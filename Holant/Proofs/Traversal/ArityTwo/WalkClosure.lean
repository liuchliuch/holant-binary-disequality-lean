import Holant.Proofs.Traversal.ArityTwo.Frontier


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
open Holant Holant.Complexity
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

structure Completion (boundary : Option (r.Ports arity)) (seen : List (r.Ports arity))
    (w : List (r.Ports arity) × Stop (r.Ports arity)) : Prop where
  almost : AlmostClosed r h boundary (w.1++seen)
  repeated : ∀ q, w.2 = .repeated q → boundary = some q ∧ Closed r h (w.1++seen)
  fresh : ∀ q ∈ w.1, ¬ Covered r seen q
  distinct : (w.1.map Sigma.fst).Nodup

private theorem covered_rotate (p : r.Ports arity) (xs seen : List (r.Ports arity))
    (q : r.Ports arity) :
    Covered r ((p::xs)++seen) q ↔ Covered r (xs++p::seen) q := by
  simp only [List.cons_append,covered_cons,covered_append]
  tauto

private theorem fresh_vertex_nodup (p : r.Ports arity) (xs : List (r.Ports arity))
    (hf : ∀ q ∈ xs, ¬ Covered r [p] q) (hn : (xs.map Sigma.fst).Nodup) :
    ((p::xs).map Sigma.fst).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_,hn⟩
  intro hp
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hp
  exact hf q hq ⟨p,by simp,he.symm⟩

theorem walk_completion (hd : ∀ v, degree (arity := arity) r v ≤ 2) (fuel : ℕ)
    (boundary : Option (r.Ports arity)) (seen : List (r.Ports arity)) (p : r.Ports arity)
    (F : Frontier r h boundary seen p)
    (hne : (walk r h fuel seen p).2 ≠ .exhausted) :
    Completion r h boundary seen (walk r h fuel seen p) := by
  induction fuel generalizing seen p with
  | zero => exact (hne rfl).elim
  | succ fuel ih =>
    have hp : p ∉ seen := F.not_mem r h
    cases ho : other r p with
    | none =>
      have hw : walk r h (fuel+1) seen p = ([p],.terminal p) := by simp [walk,hp,ho]
      rw [hw]
      refine ⟨F.finish_unary r h (terminal_unary r hd p ho),?_,?_,by simp⟩
      · intro q hq
        cases hq
      · intro q hq
        have he : q = p := by simpa using hq
        subst q
        exact F.fresh
    | some out =>
      have hw : walk r h (fuel+1) seen p =
          (p::(walk r h fuel (p::seen) (cross r h out)).1,
            (walk r h fuel (p::seen) (cross r h out)).2) := by simp [walk,hp,ho]
      rw [hw] at hne ⊢
      rcases F.next_fresh_or_boundary r h ho with hf | hb
      · have Ft := F.extend r h ho hf
        have ht := ih (p::seen) (cross r h out) Ft hne
        refine ⟨?_,?_,?_,?_⟩
        · intro q hq
          rcases ht.almost q ((covered_rotate r p _ seen q).mp hq) with hb | hc
          · exact Or.inl hb
          · exact Or.inr ((covered_rotate r p _ seen _).mpr hc)
        · intro q hq
          obtain ⟨hb,hc⟩ := ht.repeated q hq
          refine ⟨hb,?_⟩
          intro z hz
          exact (covered_rotate r p _ seen _).mpr (hc z ((covered_rotate r p _ seen z).mp hz))
        · intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact F.fresh
          · intro hc
            exact ht.fresh q hq ((covered_cons r p seen q).mpr (Or.inr hc))
        · apply fresh_vertex_nodup r p _ _ ht.distinct
          intro q hq hc
          rcases hc with ⟨z,hz,he⟩
          have hz' : z = p := by simpa using hz
          subst z
          exact ht.fresh q hq ((covered_cons r p seen q).mpr (Or.inl he))
      · have hm : cross r h out ∈ p::seen := List.mem_cons_of_mem p (F.boundary_mem _ hb)
        cases fuel with
        | zero => exact (hne rfl).elim
        | succ fuel =>
          have ht : walk r h (fuel+1) (p::seen) (cross r h out) =
              ([],.repeated (cross r h out)) := by simp [walk,hm]
          rw [ht]
          have hc := F.finish_cycle r h ho hb
          refine ⟨?_,?_,?_,by simp⟩
          · intro q hq
            exact Or.inr (hc q hq)
          · intro q hq
            cases hq
            exact ⟨hb,hc⟩
          · intro q hq
            have he : q = p := by simpa using hq
            subst q
            exact F.fresh

theorem unary_frontier (p : r.Ports arity) (hp : degree (arity := arity) r p.1 = 1) :
    Frontier r h none [p] (cross r h p) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro hc
    have hv : p.1 = (cross r h p).1 := by simpa using hc
    exact unary_cross_vertex_ne r h p hp hv.symm
  · rw [cross_cross]
    exact covered_of_mem r (by simp)
  · intro q hq
    have hv : p.1 = q.1 := by simpa using hq
    have he := same_unary_vertex r p q hp hv.symm
    subst q
    exact Or.inr (Or.inr rfl)
  · intro q hq
    cases hq

/-- A unary-started walk really terminates at a unary occurrence and covers a
cross-closed set of entire vertices, with no vertex repeated in its output. -/
theorem path_completion (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    let w := walk r h (2*r.edges.length+1) [p] (cross r h p)
    (∃ q, w.2 = .terminal q ∧ degree (arity := arity) r q.1 = 1) ∧
      Closed r h (p::w.1) ∧ ((p::w.1).map Sigma.fst).Nodup := by
  let w := walk r h (2*r.edges.length+1) [p] (cross r h p)
  have ht := walk_completion r h hd _ none [p] (cross r h p) (unary_frontier r h p hp)
    (walk_not_exhausted r h [p] (cross r h p))
  have hstop : ∃ q, w.2 = .terminal q := by
    cases he : w.2 with
    | terminal q => exact ⟨q,rfl⟩
    | repeated q => have hn := (ht.repeated q he).1; contradiction
    | exhausted => exact (walk_not_exhausted r h [p] (cross r h p) he).elim
  obtain ⟨q,hq⟩ := hstop
  refine ⟨⟨q,hq,terminal_unary r hd q (walk_terminal r h _ [p] (cross r h p) q hq)⟩,?_,?_⟩
  · intro z hz
    have hm : Covered r (w.1++[p]) z := by
      simpa only [covered_append,covered_cons,covered_nil,or_false,false_or,or_comm,List.append_nil] using hz
    rcases ht.almost z hm with he | hc
    · cases he
    · simpa only [covered_append,covered_cons,covered_nil,or_false,false_or,or_comm,List.append_nil] using hc
  · exact fresh_vertex_nodup r p w.1 ht.fresh ht.distinct

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
