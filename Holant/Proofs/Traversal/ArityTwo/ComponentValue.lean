import Holant.Proofs.Traversal.ArityTwo.WordSum


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
open Holant Holant.Complexity PortWalk Descriptors
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
variable {s b : ℕ} {arity : ℕ → ℕ} {K : Type} [CommSemiring K]
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)
variable (signatures : (i : Fin s) → Signature K (arity i.val)) (kernels : Fin b → Kernel K)

theorem cycle_denote_matrix (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1)
    (ms : List (Kernel K))
    (hm : cycleMatrices r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels)
      (walk r h (2*r.edges.length+1) [] p).1 = some ms) :
    ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h p.1)).denote Fin.elim0 =
      cycleValue ms := by
  classical
  let xs := (walk r h (2*r.edges.length+1) [] p).1
  let word := portWord r xs
  have hc := cycle_completion r h hd p hp hu
  have ht := walk_trace r h _ [] p (walk_not_exhausted r h _ _)
  rw [hc.1] at ht
  have hn : word.Nodup := portWord_nodup r hd xs hc.2.2
  have hmem : ∀ q, q ∈ word ↔ (r.shape h).componentOf q.1 = Comp r h p.1 := fun q =>
    (portWord_mem r hd xs q).trans ((covered_iff_vertex_mem r xs q).trans
      ((cycle_vertex_coverage r h hd p hp hu q.1).trans (vertex_fiber r h p q.1)))
  let pe := wordEquiv r h p.1 word hn hmem
  let ae := Equiv.arrowCongr pe (Equiv.refl Bool)
  have hhead : ∃ rest, word = p::rest := by
    obtain ⟨tail,hxs,_⟩ := cycle_cross_departures r h hd p hp hu
    change ∃ rest, portWord r xs = p::rest
    change xs = p::tail at hxs
    rw [hxs]
    exact ⟨_,rfl⟩
  obtain ⟨rest,hhead⟩ := hhead
  have hlen : word.length = ms.length :=
    (repeated_word_length r h ht).trans (cycleMatrices_length r h _ _ xs ms hm).symm
  have hms : ms ≠ [] := by
    intro he
    have hl := congrArg List.length hhead
    rw [he,List.length_nil] at hlen
    simp only [List.length_cons] at hl
    omega
  rw [cycle_component_sum r h signatures kernels hd p hp hu]
  calc
    _ = ∑ bits : Fin word.length → Bool,
        walkWeight r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels) id
          (liftAssignment r h p.1 (ae bits)) xs :=
      (ae.sum_comp (fun z => walkWeight r h (occurrenceVertex r h signatures)
        (occurrenceEdge r h kernels) id (liftAssignment r h p.1 z) xs)).symm
    _ = ∑ bits : Fin word.length → Bool, cycleWordValue ms (List.ofFn bits) := by
      apply Finset.sum_congr rfl
      intro bits _
      let z := liftAssignment r h p.1 (ae bits)
      have hw := cycleMatrices_weight r h (occurrenceVertex r h signatures)
        (occurrenceEdge r h kernels) id z ht ms hm
      simp only [map_realizeMatrix_id] at hw
      have hbits : word.map z = List.ofFn bits := lift_word r h p.1 word hn hmem bits
      calc
        _ = rightValue (fun _ => 1) ms (word.map z++[z p]) := hw.symm
        _ = cycleWordValue ms (word.map z) := by rw [hhead]; rfl
        _ = _ := by rw [hbits]
    _ = ∑ bits : Fin ms.length → Bool, cycleWordValue ms (List.ofFn bits) :=
      sum_words_congr_length hlen (cycleWordValue ms)
    _ = cycleValue ms := sum_cycleWordValue ms hms

theorem path_denote_matrix (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) (ms : List (Kernel K)) (right : Bool → K)
    (hm : pathMatrices r h (occurrenceVertex r h signatures) (occurrenceEdge r h kernels)
      (walk r h (2*r.edges.length+1) [p] (cross r h p)).1 = some (ms,right)) :
    ((r.realize h signatures kernels).componentFiniteNetwork (Comp r h p.1)).denote Fin.elim0 =
      pathValue (unaryTable r (occurrenceVertex r h signatures) p.1)
        (edgeTable r h (occurrenceEdge r h kernels) p::ms) right := by
  classical
  let xs := (walk r h (2*r.edges.length+1) [p] (cross r h p)).1
  let word := portWord r (p::xs)
  let left := unaryTable r (occurrenceVertex r h signatures) p.1
  let matrices := edgeTable r h (occurrenceEdge r h kernels) p::ms
  obtain ⟨q,hq,_⟩ := (path_completion r h hd p hp).1
  have ht := walk_trace r h _ [p] (cross r h p) (walk_not_exhausted r h _ _)
  rw [hq] at ht
  have hc := path_completion r h hd p hp
  have hn : word.Nodup := portWord_nodup r hd (p::xs) hc.2.2
  have hmem : ∀ q, q ∈ word ↔ (r.shape h).componentOf q.1 = Comp r h p.1 := fun q =>
    (portWord_mem r hd (p::xs) q).trans ((covered_iff_vertex_mem r (p::xs) q).trans
      ((path_vertex_coverage r h hd p hp q.1).trans (vertex_fiber r h p q.1)))
  let pe := wordEquiv r h p.1 word hn hmem
  let ae := Equiv.arrowCongr pe (Equiv.refl Bool)
  have ho : other r p = none := (other_none_iff r p).mpr (by omega)
  obtain ⟨rest,hhead⟩ := terminal_word_head r h ht
  have hlen : word.length = matrices.length+1 := by
    have hw := terminal_word_length r h ht
    have hm' := pathMatrices_length r h _ _ xs ms right hm
    dsimp [word,matrices]
    simp only [portWord,ho,Option.toList_none,List.nil_append,List.cons_append,List.nil_append,List.length_cons]
    change (portWord r xs).length + 1 = 2 * xs.length at hw
    omega
  rw [path_component_sum r h signatures kernels hd p hp]
  calc
    _ = ∑ bits : Fin word.length → Bool,
        listTerm r h signatures kernels p.1 (p::xs) (p::departures r xs) (ae bits) :=
      (ae.sum_comp (fun z => listTerm r h signatures kernels p.1 (p::xs) (p::departures r xs) z)).symm
    _ = ∑ bits : Fin word.length → Bool, pathWordValue left right matrices (List.ofFn bits) := by
      apply Finset.sum_congr rfl
      intro bits _
      let z := liftAssignment r h p.1 (ae bits)
      have hw := pathMatrices_weight r h (occurrenceVertex r h signatures)
        (occurrenceEdge r h kernels) id hd z ht ms right hm
      simp only [map_realizeMatrix_id,id_eq] at hw
      rw [hhead] at hw
      simp only [List.map_cons] at hw
      have hl := unaryTable_at_assignment r (occurrenceVertex r h signatures) id z p hp
      have he := edgeTable_at_assignment r h (occurrenceEdge r h kernels) id z p
      simp only [realizeMatrix_id,id_eq] at hl he
      have hbits : word.map z = List.ofFn bits := lift_word r h p.1 word hn hmem bits
      rw [← hbits]
      change _ = pathWordValue left right matrices ((portWord r (p::xs)).map z)
      simp only [portWord,ho,Option.toList_none,List.nil_append,List.cons_append,List.nil_append,show portWord r xs = cross r h p :: rest from hhead,List.map_cons,
        pathWordValue,matrices,rightValue]
      rw [he,hw]
      change _ = unaryTable r (occurrenceVertex r h signatures) p.1 (z p) * _
      rw [hl]
      simp only [listTerm,walkWeight,List.map_cons,List.prod_cons]
      dsimp only [xs,z,vertexWeight,edgeWeight,id_eq]
      ac_rfl
    _ = ∑ bits : Fin (matrices.length+1) → Bool, pathWordValue left right matrices (List.ofFn bits) :=
      sum_words_congr_length hlen (pathWordValue left right matrices)
    _ = pathValue left matrices right := sum_pathWordValue left right matrices

end Holant.LocalDrafts.TraversalCompletion.ArityTwo.OrderedDenote
