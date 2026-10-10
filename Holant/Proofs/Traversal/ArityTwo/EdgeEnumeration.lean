import Holant.Proofs.Traversal.ArityTwo.WalkTrace


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
open Holant Holant.Complexity
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

theorem vertex_unique (xs : List (r.Ports arity)) (hn : (xs.map Sigma.fst).Nodup)
    (p q : r.Ports arity) (hp : p ∈ xs) (hq : q ∈ xs) (hv : p.1 = q.1) : p = q := by
  induction xs with
  | nil => simp at hp
  | cons a xs ih =>
    obtain ⟨ha,ht⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with hpa | hpt
    · subst p
      rcases List.mem_cons.mp hq with hqa | hqt
      · exact hqa.symm
      · exact (ha (List.mem_map.mpr ⟨q,hqt,hv.symm⟩)).elim
    · rcases List.mem_cons.mp hq with hqa | hqt
      · subst q
        exact (ha (List.mem_map.mpr ⟨p,hpt,hv⟩)).elim
      · exact ih ht hpt hqt

theorem departures_mem (xs : List (r.Ports arity)) (q : r.Ports arity) :
    q ∈ departures r xs ↔ ∃ p ∈ xs, other r p = some q := by
  simp [departures,List.mem_filterMap]

theorem departures_disjoint (xs : List (r.Ports arity)) (hn : (xs.map Sigma.fst).Nodup) :
    ∀ p ∈ xs, p ∉ departures r xs := by
  intro p hp hpd
  obtain ⟨q,hq,ho⟩ := (departures_mem r xs p).mp hpd
  have he := vertex_unique r xs hn p q hp hq (other_some r q p ho).1
  exact other_ne r q p ho he

theorem departures_vertex_nodup (xs : List (r.Ports arity)) (hn : (xs.map Sigma.fst).Nodup) :
    ((departures r xs).map Sigma.fst).Nodup := by
  induction xs with
  | nil => simp [departures]
  | cons p xs ih =>
    obtain ⟨hp,ht⟩ := List.nodup_cons.mp hn
    cases ho : other r p with
    | none => simpa [departures,ho] using ih ht
    | some out =>
      simp only [departures,List.filterMap_cons,ho,List.map_cons]
      apply List.nodup_cons.mpr
      refine ⟨?_,ih ht⟩
      intro hm
      obtain ⟨q,hq,hv⟩ := List.mem_map.mp hm
      obtain ⟨u,hu,huo⟩ := (departures_mem r xs q).mp hq
      apply hp
      exact List.mem_map.mpr ⟨u,hu,
        (other_some r u q huo).1.symm.trans (hv.trans (other_some r p out ho).1)⟩

theorem same_edge (p q : r.Ports arity) (he : (r.route h p).1 = (r.route h q).1) :
    q = p ∨ q = cross r h p := by
  by_cases hb : (r.route h p).2 = (r.route h q).2
  · left
    exact (r.route_bijective h).1 (Prod.ext he.symm hb.symm)
  · right
    apply (r.route_bijective h).1
    rw [route_cross]
    refine Prod.ext he.symm ?_
    cases hp : (r.route h p).2 <;> cases hq : (r.route h q).2 <;> simp_all

private theorem map_nodup_on {X Y : Type*} (f : X → Y) (xs : List X) (hn : xs.Nodup)
    (hi : ∀ p ∈ xs, ∀ q ∈ xs, f p = f q → p = q) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
    obtain ⟨hp,ht⟩ := List.nodup_cons.mp hn
    apply List.nodup_cons.mpr
    refine ⟨?_,ih ht (fun a ha b hb => hi a (by simp [ha]) b (by simp [hb]))⟩
    intro hm
    obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
    exact hp ((hi q (by simp [hq]) p (by simp) he) ▸ hq)

theorem edge_ids_nodup (arrivals outs : List (r.Ports arity))
    (hn : outs.Nodup) (hc : ∀ q ∈ outs, cross r h q ∈ arrivals)
    (hd : ∀ q ∈ arrivals, q ∉ outs) : (outs.map (fun p => (r.route h p).1)).Nodup := by
  apply map_nodup_on _ outs hn
  intro p hp q hq he
  rcases same_edge r h p q he with he | he
  · exact he.symm
  · subst q
    exact (hd _ (hc p hp) hq).elim

theorem path_departure_partition (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) (q : r.Ports arity) :
    let xs := (walk r h (2*r.edges.length+1) [p] (cross r h p)).1
    Covered r (p::xs) q ↔ q ∈ xs ∨ q ∈ p::departures r xs := by
  constructor
  · intro hq
    obtain ⟨u,hu,hv⟩ := hq
    rcases List.mem_cons.mp hu with hup | hu
    · subst u
      have he := same_unary_vertex r p q hp hv.symm
      subst q
      exact Or.inr (by simp)
    · cases ho : other r u with
      | none =>
        have he := same_unary_vertex r u q (terminal_unary r hd u ho) hv.symm
        subst q
        exact Or.inl hu
      | some out =>
        rcases binary_ports r u out q ho hv.symm with hqu | hqo
        · subst q; exact Or.inl hu
        · subst q
          exact Or.inr (List.mem_cons_of_mem p ((departures_mem r _ out).mpr ⟨u,hu,ho⟩))
  · rintro (hq | hq)
    · exact covered_of_mem r (List.mem_cons_of_mem p hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact covered_of_mem r (by simp)
      · obtain ⟨u,hu,ho⟩ := (departures_mem r _ q).mp hq
        exact ⟨u,List.mem_cons_of_mem p hu,(other_some r u q ho).1.symm⟩

theorem path_edge_ids_nodup (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    let xs := (walk r h (2*r.edges.length+1) [p] (cross r h p)).1
    ((p::departures r xs).map (fun q => (r.route h q).1)).Nodup := by
  let xs := (walk r h (2*r.edges.length+1) [p] (cross r h p)).1
  have hv := (path_completion r h hd p hp).2.2
  have htail := (List.nodup_cons.mp hv).2
  have hc : (p::departures r xs).map (cross r h) = xs := path_cross_departures r h hd p hp
  have hdis : ∀ q ∈ xs, q ∉ p::departures r xs := by
    intro q hq hqd
    rcases List.mem_cons.mp hqd with hqp | hqd
    · subst q
      exact (List.nodup_cons.mp hv).1 (List.mem_map.mpr ⟨p,hq,rfl⟩)
    · exact departures_disjoint r xs htail q hq hqd
  apply edge_ids_nodup r h xs (p::departures r xs) _ _ hdis
  · apply List.Nodup.of_map (f := cross r h)
    rw [hc]
    exact List.Nodup.of_map Sigma.fst htail
  · intro q hq
    rw [← hc]
    exact List.mem_map.mpr ⟨q,hq,rfl⟩

theorem cycle_departure_partition (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1)
    (q : r.Ports arity) :
    let xs := (walk r h (2*r.edges.length+1) [] p).1
    Covered r xs q ↔ q ∈ xs ∨ q ∈ departures r xs := by
  have ht := walk_trace r h _ [] p (walk_not_exhausted r h _ _)
  rw [(cycle_completion r h hd p hp hu).1] at ht
  constructor
  · rintro ⟨u,hm,hv⟩
    obtain ⟨out,ho⟩ := other_exists r u (ht.repeated_binary r h u hm)
    rcases binary_ports r u out q ho hv.symm with hqu | hqo
    · subst q; exact Or.inl hm
    · subst q
      exact Or.inr ((departures_mem r _ out).mpr ⟨u,hm,ho⟩)
  · rintro (hm | hm)
    · exact covered_of_mem r hm
    · obtain ⟨u,hm,ho⟩ := (departures_mem r _ q).mp hm
      exact ⟨u,hm,(other_some r u q ho).1.symm⟩

theorem cycle_cross_mem (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1)
    (q : r.Ports arity) :
    let xs := (walk r h (2*r.edges.length+1) [] p).1
    q ∈ xs ↔ cross r h q ∈ departures r xs := by
  obtain ⟨tail,hxs,hcross⟩ := cycle_cross_departures r h hd p hp hu
  rw [hxs]
  have he : q ∈ (departures r (p::tail)).map (cross r h) ↔
      cross r h q ∈ departures r (p::tail) := by
    constructor
    · intro hm
      obtain ⟨out,ho,he⟩ := List.mem_map.mp hm
      rw [← he,cross_cross]
      exact ho
    · intro hq
      exact List.mem_map.mpr ⟨cross r h q,hq,cross_cross r h q⟩
  rw [hcross] at he
  simpa [List.mem_append,or_comm] using he

theorem cycle_edge_ids_nodup (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1) :
    let xs := (walk r h (2*r.edges.length+1) [] p).1
    ((departures r xs).map (fun q => (r.route h q).1)).Nodup := by
  let xs := (walk r h (2*r.edges.length+1) [] p).1
  have hv := (cycle_completion r h hd p hp hu).2.2
  apply edge_ids_nodup r h xs (departures r xs)
    (List.Nodup.of_map Sigma.fst (departures_vertex_nodup r xs hv)) _ (departures_disjoint r xs hv)
  intro q hq
  apply (cycle_cross_mem r h hd p hp hu (cross r h q)).mpr
  simpa only [cross_cross] using hq

private theorem edge_mem_iff_covered (full arrivals outs : List (r.Ports arity))
    (closed : Closed r h full)
    (partition : ∀ q, Covered r full q ↔ q ∈ arrivals ∨ q ∈ outs)
    (crossing : ∀ q, q ∈ arrivals ↔ cross r h q ∈ outs)
    (e : Fin r.edges.length) :
    e ∈ outs.map (fun q => (r.route h q).1) ↔ Covered r full (r.lookup h (e,false)) := by
  constructor
  · intro he
    obtain ⟨q,hq,hqe⟩ := List.mem_map.mp he
    have hqc := (partition q).mpr (Or.inr hq)
    have hid : (r.route h q).1 = (r.route h (r.lookup h (e,false))).1 := by simpa using hqe
    rcases same_edge r h q (r.lookup h (e,false)) hid with hq' | hq'
    · simpa only [hq'] using hqc
    · simpa only [hq'] using closed q hqc
  · intro he
    rcases (partition _).mp he with ha | ho
    · refine List.mem_map.mpr ⟨cross r h (r.lookup h (e,false)),(crossing _).mp ha,?_⟩
      simp
    · exact List.mem_map.mpr ⟨r.lookup h (e,false),ho,by simp⟩

/-- Exact original edge enumeration for a path: membership and uniqueness
are both proved for the actual departure list. -/
theorem path_edge_exact (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) (e : Fin r.edges.length) :
    let xs := (walk r h (2*r.edges.length+1) [p] (cross r h p)).1
    e ∈ (p::departures r xs).map (fun q => (r.route h q).1) ↔
      (r.graph h).label (r.lookup h (e,false)).1 = (r.graph h).label p.1 := by
  let xs := (walk r h (2*r.edges.length+1) [p] (cross r h p)).1
  have hc : (p::departures r xs).map (cross r h) = xs := path_cross_departures r h hd p hp
  have hcross : ∀ q, q ∈ xs ↔ cross r h q ∈ p::departures r xs := by
    intro q
    conv_lhs => rw [← hc]
    constructor
    · intro hq
      obtain ⟨out,ho,he⟩ := List.mem_map.mp hq
      rw [← he,cross_cross]
      exact ho
    · intro hq
      exact List.mem_map.mpr ⟨cross r h q,hq,cross_cross r h q⟩
  change e ∈ (p::departures r xs).map (fun q => (r.route h q).1) ↔ _
  rw [edge_mem_iff_covered r h (p::xs) xs (p::departures r xs)
    (path_completion r h hd p hp).2.1 (path_departure_partition r h hd p hp) hcross e,
    covered_iff_vertex_mem]
  exact path_vertex_coverage r h hd p hp (r.lookup h (e,false)).1

theorem cycle_edge_exact (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1)
    (e : Fin r.edges.length) :
    let xs := (walk r h (2*r.edges.length+1) [] p).1
    e ∈ (departures r xs).map (fun q => (r.route h q).1) ↔
      (r.graph h).label (r.lookup h (e,false)).1 = (r.graph h).label p.1 := by
  dsimp only
  rw [edge_mem_iff_covered r h _ _ _ (cycle_completion r h hd p hp hu).2.1
    (cycle_departure_partition r h hd p hp hu) (cycle_cross_mem r h hd p hp hu) e,
    covered_iff_vertex_mem,cycle_vertex_coverage r h hd p hp hu]

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
