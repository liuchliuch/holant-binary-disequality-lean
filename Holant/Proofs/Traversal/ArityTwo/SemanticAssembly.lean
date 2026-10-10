import Holant.Proofs.Traversal.ArityTwo.ComponentValue


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
open Holant Holant.Complexity PortWalk Descriptors
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {s b : ℕ} {arity : ℕ → ℕ} {K : Type} [CommSemiring K]
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (signatures : (i : Fin s) → Signature K (arity i.val)) (kernels : Fin b → Kernel K)

theorem pathFrom_correct (hd : ∀ v, degree (arity := arity) r v ≤ 2) (v : Fin r.vertices.length)
    (hv : degree (arity := arity) r v = 1) (c : Component K)
    (hc : pathFrom r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels) v hv = some c) :
    c.eval id = ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h v)).denote Fin.elim0 := by
  let p : r.Ports arity := ⟨v,⟨0,by change arity (r.vertices.get v).1 = 1 at hv; omega⟩⟩
  obtain ⟨q,hq,_⟩ := (path_completion r h hd p hv).1
  have ht := walk_trace r h (2*r.edges.length+1) [p] (cross r h p) (walk_not_exhausted r h _ _)
  rw [hq] at ht
  obtain ⟨ms,right,hm⟩ := pathMatrices_trace r h (occurrenceVertex r h signatures)
    (occurrenceEdge r h kernels) hd ht
  have he : c = .path (unaryTable r (occurrenceVertex r h signatures) v)
      (edgeTable r h (occurrenceEdge r h kernels) p::ms) right := by
    have hh : pathFrom r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels) v hv =
        some (.path (unaryTable r (occurrenceVertex r h signatures) v)
          (edgeTable r h (occurrenceEdge r h kernels) p::ms) right) := by
      change (match (walk r h (2*r.edges.length+1) [p] (cross r h p)).2 with
        | .terminal _ => (pathMatrices r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels)
            (walk r h (2*r.edges.length+1) [p] (cross r h p)).1).bind
            (fun t => some (Component.path (unaryTable r (occurrenceVertex r h signatures) v)
              (edgeTable r h (occurrenceEdge r h kernels) p::t.1) t.2))
        | _ => none) = _
      rw [hq,hm]
      rfl
    exact Option.some.inj (hc.symm.trans hh)
  rw [he]
  simpa only [Component.eval,map_realizeMatrix_id,id_eq] using
    (path_denote_matrix r h signatures kernels hd p hv ms right hm).symm

theorem cycleFrom_correct (hd : ∀ v, degree (arity := arity) r v ≤ 2) (v : Fin r.vertices.length)
    (hv : degree (arity := arity) r v = 2)
    (hu : ∀ w, (r.graph h).label w = (r.graph h).label v → degree (arity := arity) r w ≠ 1)
    (c : Component K)
    (hc : cycleFrom r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels) v hv = some c) :
    c.eval id = ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h v)).denote Fin.elim0 := by
  let p : r.Ports arity := ⟨v,⟨0,by change arity (r.vertices.get v).1 = 2 at hv; omega⟩⟩
  have hclose := (cycle_completion r h hd p hv hu).1
  have ht := walk_trace r h (2*r.edges.length+1) [] p (walk_not_exhausted r h _ _)
  rw [hclose] at ht
  obtain ⟨ms,hm⟩ := cycleMatrices_trace r h (occurrenceVertex r h signatures)
    (occurrenceEdge r h kernels) ht
  dsimp only [p] at hclose hm
  simp only [cycleFrom,fuel,hclose,↓reduceIte,hm,Option.bind_some] at hc
  cases ms with
  | nil => cases hc
  | cons M ms =>
    have he : c = .cycle M ms := (Option.some.inj hc).symm
    rw [he]
    simpa only [Component.eval,map_realizeMatrix_id] using
      (cycle_denote_matrix r h signatures kernels hd p hv hu (M::ms) hm).symm

private theorem find_some_mem {X : Type*} (P : X → Bool) (xs : List X) (x : X)
    (hx : xs.find? P = some x) : x ∈ xs := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    cases hp : P y with
    | false => exact List.mem_cons_of_mem y (ih (by simpa [List.find?,hp] using hx))
    | true => have he : y = x := by simpa [List.find?,hp] using hx
              simp [he]

private theorem find_none_not {X : Type*} (P : X → Bool) (xs : List X)
    (hx : xs.find? P = none) : ∀ x ∈ xs, P x = false := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    cases hp : P y with
    | true => simp [List.find?,hp] at hx
    | false =>
      intro x hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hp
      · exact ih (by simpa [List.find?,hp] using hx) x hm

theorem component_correct (hd : ∀ v, degree (arity := arity) r v ≤ 2) (root : Fin r.vertices.length)
    (hr : root ∈ (r.graph h).roots) (c : Component K)
    (hc : component r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels) root = some c) :
    c.eval id = ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h root)).denote Fin.elim0 := by
  have hroot := ((r.graph h).mem_roots root).mp hr
  cases hs : ((r.graph h).componentVertices root).find? (fun v => decide (degree (arity := arity) r v = 1)) with
  | some v =>
    have hv : degree (arity := arity) r v = 1 := of_decide_eq_true (List.find?_some (p := fun v => decide (degree (arity := arity) r v = 1)) hs)
    have hm := find_some_mem _ _ v hs
    have hl : (r.graph h).label v = (r.graph h).label root := by
      rw [hroot]
      exact ((r.graph h).mem_componentVertices root v).mp hm
    have he := (r.graph_label_eq_iff h v root).mp hl
    simp only [component,hs,dif_pos hv] at hc
    exact (pathFrom_correct r h signatures kernels hd v hv c hc).trans
      (congrArg (fun k => ((r.realize h signatures kernels).componentFiniteNetwork k).denote Fin.elim0) he)
  | none =>
    have hu : ∀ v, (r.graph h).label v = (r.graph h).label root → degree (arity := arity) r v ≠ 1 := by
      intro v hv
      have hm : v ∈ (r.graph h).componentVertices root :=
        ((r.graph h).mem_componentVertices root v).mpr (hv.trans hroot)
      have hh := find_none_not _ _ hs v hm
      simpa only [decide_eq_false_iff_not] using hh
    by_cases hz : degree (arity := arity) r root = 0
    · have he : c = .scalar (occurrenceVertex r h signatures root (fun _ => false)) := by
        simp only [component,hs,if_pos hz] at hc
        exact (Option.some.inj hc).symm
      rw [he]
      exact (nullary_component_denote r h signatures kernels root hz).symm
    · have hb : degree (arity := arity) r root = 2 := by have hle := hd root; have hn := hu root rfl; omega
      simp only [component,hs,if_neg hz,dif_pos hb] at hc
      exact cycleFrom_correct r h signatures kernels hd root hb hu c hc

theorem all_correct (hd : ∀ v, degree (arity := arity) r v ≤ 2) (cs : List (Component K))
    (hc : all r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels) = some cs) :
    evaluateComponents id cs = (r.realize h signatures kernels).denote Fin.elim0 := by
  classical
  let value := fun root => ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h root)).denote Fin.elim0
  have aux (roots : List (Fin r.vertices.length)) (hr : ∀ root ∈ roots, root ∈ (r.graph h).roots)
      (cs : List (Component K))
      (hc : roots.mapM (component r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels)) = some cs) :
      evaluateComponents id cs = (roots.map value).prod := by
    induction roots generalizing cs with
    | nil => have he : cs = [] := by simpa using hc.symm
             subst cs
             rfl
    | cons root roots ih =>
      obtain ⟨c,hc₀⟩ := component_total r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels)
        hd root (hr root (by simp))
      cases htail : roots.mapM (component r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels)) with
      | none => simp [hc₀,htail] at hc
      | some tail =>
        have he : cs = c::tail := by simpa [hc₀,htail] using hc.symm
        subst cs
        have ht := ih (fun v hv => hr v (List.mem_cons_of_mem root hv)) tail htail
        have hv := component_correct r h signatures kernels hd root (hr root (by simp)) c hc₀
        simp only [evaluateComponents,List.map_cons,List.prod_cons] at ht ⊢
        rw [hv,ht]
  rw [aux _ (fun _ h => h) cs hc,raw_denote_roots r h signatures kernels]
  exact (prod_get (r.graph h).roots value).symm

/-- Derived completeness and the original denotation in one statement. -/
theorem extract_correct (hd : ∀ v, degree (arity := arity) r v ≤ 2) :
    ∃ cs, all r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels) = some cs ∧
      evaluateComponents id cs = (r.realize h signatures kernels).denote Fin.elim0 := by
  obtain ⟨cs,hcs⟩ := all_total r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels) hd
  exact ⟨cs,hcs,all_correct r h signatures kernels hd cs hcs⟩

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
