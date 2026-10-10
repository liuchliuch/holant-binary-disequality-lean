import Holant.Proofs.Traversal.ArityTwo.Cycles


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
open Holant Holant.Complexity
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

inductive Trace : r.Ports arity → List (r.Ports arity) → Stop (r.Ports arity) → Prop
  | terminal (p) (ho : other r p = none) : Trace p [p] (.terminal p)
  | repeated (p) : Trace p [] (.repeated p)
  | step (p out xs stop) (ho : other r p = some out)
      (tail : Trace (cross r h out) xs stop) : Trace p (p::xs) stop

theorem walk_trace (fuel : ℕ) (seen : List (r.Ports arity)) (p : r.Ports arity)
    (he : (walk r h fuel seen p).2 ≠ .exhausted) :
    Trace r h p (walk r h fuel seen p).1 (walk r h fuel seen p).2 := by
  induction fuel generalizing seen p with
  | zero => exact (he rfl).elim
  | succ fuel ih =>
    by_cases hp : p ∈ seen
    · simp only [walk, if_pos hp]
      exact .repeated p
    · cases ho : other r p with
      | none =>
        simp only [walk, if_neg hp, ho]
        exact .terminal p ho
      | some out =>
        simp only [walk, if_neg hp, ho] at he ⊢
        exact .step p out _ _ ho (ih _ _ he)

def departures (xs : List (r.Ports arity)) : List (r.Ports arity) := xs.filterMap (other r)

def closing : Stop (r.Ports arity) → List (r.Ports arity)
  | .terminal _ => []
  | .repeated p => [p]
  | .exhausted => []

theorem Trace.ordered {p : r.Ports arity} {xs : List (r.Ports arity)} {stop : Stop (r.Ports arity)}
    (ht : Trace r h p xs stop) :
    xs++closing r stop = p::(departures r xs).map (cross r h) := by
  induction ht with
  | terminal p ho => simp [closing,departures,ho]
  | repeated p => rfl
  | step p out xs stop ho ht ih =>
    simpa [departures,ho,List.cons_append] using congrArg (List.cons p) ih

theorem Trace.terminal_mem {p q : r.Ports arity} {xs : List (r.Ports arity)}
    (ht : Trace r h p xs (.terminal q)) : q ∈ xs := by
  have aux : ∀ {p xs stop}, Trace r h p xs stop → ∀ q, stop = .terminal q → q ∈ xs := by
    intro p xs stop ht
    induction ht with
    | terminal p ho => intro q he; cases he; simp
    | repeated p => intro q he; cases he
    | step p out xs stop ho ht ih =>
      intro q he
      exact List.mem_cons_of_mem p (ih q he)
  exact aux ht q rfl

theorem Trace.repeated_binary {p q : r.Ports arity} {xs : List (r.Ports arity)}
    (ht : Trace r h p xs (.repeated q)) : ∀ v ∈ xs, degree (arity := arity) r v.1 = 2 := by
  have aux : ∀ {p xs stop}, Trace r h p xs stop →
      ∀ q, stop = .repeated q → ∀ v ∈ xs, degree (arity := arity) r v.1 = 2 := by
    intro p xs stop ht
    induction ht with
    | terminal p ho => intro q he; cases he
    | repeated p => intro q he v hv; cases hv
    | step p out xs stop ho ht ih =>
      intro q he v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact (other_some r v out ho).2.2
      · exact ih q he v hv
  exact aux ht q rfl

theorem path_cross_departures (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    let xs := (walk r h (2*r.edges.length+1) [p] (cross r h p)).1
    (p::departures r xs).map (cross r h) = xs := by
  obtain ⟨q,hq,_⟩ := (path_completion r h hd p hp).1
  have ht := walk_trace r h _ [p] (cross r h p) (walk_not_exhausted r h _ _)
  rw [hq] at ht
  simpa [closing] using (ht.ordered r h).symm

theorem cycle_cross_departures (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1) :
    ∃ tail, (walk r h (2*r.edges.length+1) [] p).1 = p::tail ∧
      (departures r (p::tail)).map (cross r h) = tail++[p] := by
  have hc := cycle_completion r h hd p hp hu
  have ht := walk_trace r h _ [] p (walk_not_exhausted r h _ _)
  rw [hc.1] at ht
  have hm := walk_start_mem r h (2*r.edges.length+1) (by omega) [] p (by simp)
  cases hx : (walk r h (2*r.edges.length+1) [] p).1 with
  | nil => simp [hx] at hm
  | cons q tail =>
    have he := walk_head r h _ [] p q tail hx
    subst q
    refine ⟨tail,rfl,?_⟩
    have ho := ht.ordered r h
    rw [hx] at ho
    simpa [closing] using ho.symm

/-- Terminal unary vertices differ even as original vertex IDs. -/
theorem path_distinct_endpoints (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p q : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1)
    (hq : (walk r h (2*r.edges.length+1) [p] (cross r h p)).2 = .terminal q) : q.1 ≠ p.1 := by
  have ht := walk_trace r h _ [p] (cross r h p) (walk_not_exhausted r h _ _)
  rw [hq] at ht
  have hm := ht.terminal_mem r h
  have hc := walk_completion r h hd _ none [p] (cross r h p) (unary_frontier r h p hp)
    (walk_not_exhausted r h _ _)
  intro hv
  exact hc.fresh q hm ⟨p,by simp,hv.symm⟩

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
