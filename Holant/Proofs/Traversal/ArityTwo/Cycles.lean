import Holant.Proofs.Traversal.ArityTwo.Coverage


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
open Holant Holant.Complexity Holant.OneHot.Computable
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

theorem other_exists (p : r.Ports arity) (hp : degree (arity := arity) r p.1 = 2) :
    ∃ out, other r p = some out := by
  cases ho : other r p with
  | none => exact ((other_none_iff r p).mp ho hp).elim
  | some out => exact ⟨out,rfl⟩

theorem binary_frontier (p out : r.Ports arity) (ho : other r p = some out)
    (hn : cross r h out ≠ p) : Frontier r h (some p) [p] (cross r h out) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro hc
    have hv : p.1 = (cross r h out).1 := by simpa [eq_comm] using hc
    rcases binary_ports r p out (cross r h out) ho hv.symm with he | he
    · exact hn he
    · exact cross_ne r h out he
  · rw [cross_cross,covered_iff_vertex_mem]
    simpa using (other_some r p out ho).1
  · intro q hq
    have hv : p.1 = q.1 := by simpa [eq_comm] using hq
    rcases binary_ports r p out q ho hv.symm with hqp | hqo
    · exact Or.inl (congrArg some hqp.symm)
    · exact Or.inr (Or.inr (congrArg (cross r h) hqo))
  · intro q hq
    cases hq
    simp

theorem walk_start_mem (fuel : ℕ) (hf : 0 < fuel) (seen : List (r.Ports arity))
    (p : r.Ports arity) (hp : p ∉ seen) : p ∈ (walk r h fuel seen p).1 := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    simp only [walk,if_neg hp]
    split <;> simp

theorem cycle_completion (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1) :
    let w := walk r h (2*r.edges.length+1) [] p
    w.2 = .repeated p ∧ Closed r h w.1 ∧ (w.1.map Sigma.fst).Nodup := by
  obtain ⟨out,ho⟩ := other_exists r p hp
  have hw : walk r h (2*r.edges.length+1) [] p =
      (p::(walk r h (2*r.edges.length) [p] (cross r h out)).1,
        (walk r h (2*r.edges.length) [p] (cross r h out)).2) := by simp [walk,ho]
  have hne := walk_not_exhausted r h [] p
  rw [hw] at hne ⊢
  by_cases he : cross r h out = p
  · have hepos : 0 < r.edges.length := Nat.zero_lt_of_lt (r.route h p).1.isLt
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show 2*r.edges.length ≠ 0 by omega)
    have ht : walk r h (2*r.edges.length) [p] (cross r h out) = ([],.repeated p) := by
      rw [hk,he]
      simp [walk]
    rw [ht]
    refine ⟨rfl,?_,by simp⟩
    intro q hq
    have hv : p.1 = q.1 := by simpa [eq_comm] using hq
    rcases binary_ports r p out q ho hv.symm with hqp | hqo
    · subst q
      have hc : cross r h p = out := by rw [← he,cross_cross]
      rw [hc,covered_iff_vertex_mem]
      simpa using (other_some r p out ho).1
    · subst q
      rw [he]
      exact covered_of_mem r (by simp)
  · have ht := walk_completion r h hd _ (some p) [p] (cross r h out)
      (binary_frontier r h p out ho he) hne
    have hs : (walk r h (2*r.edges.length) [p] (cross r h out)).2 = .repeated p := by
      cases hx : (walk r h (2*r.edges.length) [p] (cross r h out)).2 with
      | exhausted => exact (hne hx).elim
      | terminal q =>
        have hq := terminal_unary r hd q (walk_terminal r h _ [p] (cross r h out) q hx)
        have hl := (walk_terminal_label r h _ [p] (cross r h out) q hx).trans
          (label_next r h p out ho)
        exact (hu q.1 hl hq).elim
      | repeated q =>
        have hq : p = q := Option.some.inj (ht.repeated q hx).1
        cases hq
        rfl
    refine ⟨hs,?_,?_⟩
    · have hc := (ht.repeated p hs).2
      intro q hq
      have hm : Covered r ((walk r h (2*r.edges.length) [p] (cross r h out)).1++[p]) q := by
        simpa only [covered_append,covered_cons,covered_nil,or_false,false_or,or_comm] using hq
      have hh := hc q hm
      simpa only [covered_append,covered_cons,covered_nil,or_false,false_or,or_comm] using hh
    · apply List.nodup_cons.mpr
      refine ⟨?_,ht.distinct⟩
      intro hm
      obtain ⟨q,hq,hv⟩ := List.mem_map.mp hm
      exact ht.fresh q hq ⟨p,by simp,hv.symm⟩

theorem cycle_vertex_coverage (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1)
    (v : Fin r.vertices.length) :
    v ∈ ((walk r h (2*r.edges.length+1) [] p).1.map Sigma.fst) ↔
      (r.graph h).label v = (r.graph h).label p.1 := by
  constructor
  · intro hv
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hv
    exact walk_labels r h _ [] p q hq
  · intro hl
    have hc := (cycle_completion r h hd p hp hu).2.1
    apply (closed_component_mem r h _ hc v p.1 hl).mpr
    exact List.mem_map.mpr ⟨p,walk_start_mem r h _ (by omega) [] p (by simp),rfl⟩

theorem cycle_edge_coverage (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1)
    (e : (r.graph h).Edge) (z : Bool) :
    (r.graph h).endpoint e z ∈ ((walk r h (2*r.edges.length+1) [] p).1.map Sigma.fst) ↔
      e ∈ (r.graph h).componentEdges ((r.graph h).label p.1) := by
  rw [cycle_vertex_coverage r h hd p hp hu,(r.graph h).mem_componentEdges,
    (r.graph h).endpoint_labels]

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
