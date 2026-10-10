import Holant.Complexity.UniversalPairReduction.Surgery.Splice

/-! General validation of literal marked-vertex smoothing. All labels and every
endpoint occurrence of the original record are retained except for the one
marked row and the one explicitly removed edge. -/
namespace Holant.Complexity.UniversalPairReduction.Surgery
open FixedGadgetSubstitution Smoothing RawClosedNetwork

abbrev remainderEnds (r : RawClosedNetwork) (v : ℕ) :=
  ((r.vertices.eraseIdx v).map Prod.snd).flatten

 theorem remove_row_partition (r : RawClosedNetwork) (v : Fin r.vertices.length)
    (p q : RawEndpoint) (hrow : (r.vertices.get v).2=[p,q]) :
    (p::q::remainderEnds r v.val).Perm r.endpoints := by
  have h := ((List.getElem_cons_eraseIdx_perm v.isLt).map Prod.snd).flatten
  have hrow' : r.vertices[v.val].2=[p,q] := hrow
  simpa only [List.map_cons,List.flatten_cons,List.get_eq_getElem,hrow',
    List.cons_append,List.nil_append,remainderEnds,RawClosedNetwork.endpoints] using h

 theorem emit_endpoints (r : RawClosedNetwork) (v e : ℕ) (f : RawEndpoint → RawEndpoint) :
    (emit r v e f).endpoints=(remainderEnds r v).map f := by
  simp [RawClosedNetwork.endpoints,emit,List.map_flatten,List.map_map,Function.comp_def]

 theorem marked_endpoint_partition {s b : ℕ} {arity : ℕ → ℕ}
    (r : RawClosedNetwork) (hr : r.WellFormed s b arity) (v : Fin r.vertices.length)
    (p q : RawEndpoint) (hrow : (r.vertices.get v).2=[p,q]) :
    (p::q::remainderEnds r v.val).Perm (edgeEnds 0 r.edges.length) :=
  (remove_row_partition r v p q hrow).trans (by simpa only [expectedEndpoints_eq] using hr.2.2)

 theorem emit_labels {sourceCount targetCount b : ℕ} {sourceArity arity : ℕ → ℕ}
    (r : RawClosedNetwork) (hr : r.WellFormed sourceCount b sourceArity)
    (v e : ℕ) (f : RawEndpoint → RawEndpoint)
    (hv : ∀row∈r.vertices.eraseIdx v,row.1<targetCount ∧ row.2.length=arity row.1) :
    (∀u : Fin (emit r v e f).vertices.length,
      ((emit r v e f).vertices.get u).1<targetCount ∧
      ((emit r v e f).vertices.get u).2.length=arity ((emit r v e f).vertices.get u).1) ∧
    (∀j : Fin (emit r v e f).edges.length,(emit r v e f).edges.get j<b) := by
  constructor
  · intro u
    have hu := List.get_mem (emit r v e f).vertices u
    obtain ⟨row,hrow,heq⟩ := List.mem_map.mp hu
    rw [←heq]
    simpa using hv row hrow
  · intro j
    have hj : (emit r v e f).edges.get j∈r.edges :=
      (List.eraseIdx_sublist r.edges e).subset (List.get_mem _ j)
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hj
    rw [←hi]
    exact hr.2.1 i

 theorem smoothAt_wellFormed {sourceCount targetCount b : ℕ} {sourceArity arity : ℕ → ℕ}
    (r : RawClosedNetwork) (hr : r.WellFormed sourceCount b sourceArity)
    (v : Fin r.vertices.length) (p q : RawEndpoint)
    (hrow : (r.vertices.get v).2=[p,q])
    (hv : ∀row∈r.vertices.eraseIdx v.val,row.1<targetCount ∧ row.2.length=arity row.1) :
    (smoothAt r v.val p q).query.WellFormed targetCount b arity := by
  have hp := marked_endpoint_partition r hr v p q hrow
  have hpbound : p.1<r.edges.length := (ends_mem _ _).mp (hp.mem_iff.mp (by simp))
  have hqbound : q.1<r.edges.length := (ends_mem _ _).mp (hp.mem_iff.mp (by simp))
  unfold smoothAt
  split_ifs with he
  · have hneq : p≠q := by
      have hn := hp.symm.nodup (ends_nodup _)
      exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    have hmate : q=(p.1,!p.2) := by
      apply Prod.ext
      · exact he.symm
      · rcases p with ⟨e,a⟩
        rcases q with ⟨f,b⟩
        dsimp at he ⊢
        subst f
        cases a <;> cases b <;> simp_all
    have hl := emit_labels r hr v.val p.1 (removeLoopEndpoint p.1) hv
    refine ⟨hl.1,hl.2,?_⟩
    rw [emit_endpoints,expectedEndpoints_eq]
    change List.Perm _ (edgeEnds 0 (r.edges.eraseIdx p.1).length)
    rw [List.length_eraseIdx_of_lt hpbound]
    exact loop_partition _ p.1 hpbound p.2 _ (by simpa only [hmate] using hp)
  · have hl := emit_labels r hr v.val q.1 (spliceEndpoint p q) hv
    refine ⟨hl.1,hl.2,?_⟩
    rw [emit_endpoints,expectedEndpoints_eq]
    change List.Perm _ (edgeEnds 0 (r.edges.eraseIdx q.1).length)
    rw [List.length_eraseIdx_of_lt hqbound]
    exact splice_partition _ p q _ he hp

end Holant.Complexity.UniversalPairReduction.Surgery
