import Holant.Proofs.Traversal.ArityTwo.OrderedDenote


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
open Holant Holant.Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s b : ℕ} {arity : ℕ → ℕ}
variable (r : RawClosedNetwork) (h : r.WellFormed s b arity)

def portWord : List (r.Ports arity) → List (r.Ports arity)
  | [] => []
  | p::ps => p :: (other r p).toList ++ portWord ps

theorem portWord_mem (hd : ∀ v, degree (arity := arity) r v ≤ 2) (xs : List (r.Ports arity))
    (q : r.Ports arity) : q ∈ portWord r xs ↔ Covered r xs q := by
  induction xs with
  | nil => simp [portWord]
  | cons p ps ih =>
    rw [covered_cons]
    cases ho : other r p with
    | none =>
      have hp := terminal_unary r hd p ho
      have he : q = p ↔ p.1 = q.1 :=
        ⟨fun he => congrArg Sigma.fst he.symm,fun hv => same_unary_vertex r p q hp hv.symm⟩
      simpa [portWord,ho,he] using (or_congr Iff.rfl ih)
    | some out =>
      have he : q = p ∨ q = out ↔ p.1 = q.1 := by
        constructor
        · rintro (hqp | hqo)
          · exact congrArg Sigma.fst hqp.symm
          · subst q
            exact (other_some r p out ho).1.symm
        · intro hv
          exact binary_ports r p out q ho hv.symm
      simpa only [portWord,ho,Option.toList_some,List.cons_append,List.nil_append,
        List.mem_cons,← or_assoc,he,ih] using (Iff.rfl :
          (q = p ∨ q = out ∨ q ∈ portWord r ps) ↔ (q = p ∨ q = out ∨ q ∈ portWord r ps))

theorem portWord_nodup (hd : ∀ v, degree (arity := arity) r v ≤ 2) (xs : List (r.Ports arity))
    (hn : (xs.map Sigma.fst).Nodup) : (portWord r xs).Nodup := by
  induction xs with
  | nil => simp [portWord]
  | cons p ps ih =>
    obtain ⟨hp,ht⟩ := List.nodup_cons.mp hn
    have hnot (q : r.Ports arity) (hv : q.1 = p.1) : q ∉ portWord r ps := by
      intro hq
      have hm := (portWord_mem r hd ps q).mp hq
      have hm' := covered_same r hm hv
      exact hp ((covered_iff_vertex_mem r ps p).mp hm')
    cases ho : other r p with
    | none => simpa [portWord,ho] using List.nodup_cons.mpr ⟨hnot p rfl,ih ht⟩
    | some out =>
      simp only [portWord,ho,Option.toList_some,List.cons_append,List.nil_append]
      apply List.nodup_cons.mpr
      refine ⟨?_,List.nodup_cons.mpr ⟨hnot out (other_some r p out ho).1,ih ht⟩⟩
      intro hm
      rcases List.mem_cons.mp hm with he | hm
      · exact other_ne r p out ho he.symm
      · exact hnot p rfl hm

/-- Fiber of complete original port occurrences, including the local index. -/
abbrev ComponentPort (root : Fin r.vertices.length) :=
  {p : r.Ports arity // (r.shape h).componentOf p.1 = (r.shape h).componentOf root}

def componentPortEquiv (root : Fin r.vertices.length) :
    ComponentPort r h root ≃ ((r.shape h).ComponentEdge ((r.shape h).componentOf root) × Bool) :=
  ({ toFun := fun p => ⟨⟨p.val.1,p.property⟩,p.val.2⟩
     invFun := fun p => ⟨⟨p.1.val,p.2⟩,p.1.property⟩
     left_inv := by rintro ⟨⟨v,j⟩,hv⟩; rfl
     right_inv := by rintro ⟨⟨v,hv⟩,j⟩; rfl } :
       ComponentPort r h root ≃ (Σ v : (r.shape h).ComponentVertex ((r.shape h).componentOf root),
         Fin ((r.shape h).arity v.val))).trans
    ((r.shape h).componentClosedPorts ((r.shape h).componentOf root))

noncomputable def pathPortEquiv (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 1) :
    Fin (portWord r (p::(walk r h (2*r.edges.length+1) [p] (cross r h p)).1)).length ≃
      ((r.shape h).ComponentEdge ((r.shape h).componentOf p.1) × Bool) :=
  (OrderedDenote.listFiberEquiv _ (portWord_nodup r hd _ (path_completion r h hd p hp).2.2)
    (fun q => (r.shape h).componentOf q.1 = (r.shape h).componentOf p.1)
    (fun q => (portWord_mem r hd _ q).trans ((covered_iff_vertex_mem r _ q).trans
      ((path_vertex_coverage r h hd p hp q.1).trans (r.graph_label_eq_iff h q.1 p.1))))).trans
    (componentPortEquiv r h p.1)

noncomputable def cyclePortEquiv (hd : ∀ v, degree (arity := arity) r v ≤ 2) (p : r.Ports arity)
    (hp : degree (arity := arity) r p.1 = 2)
    (hu : ∀ v, (r.graph h).label v = (r.graph h).label p.1 → degree (arity := arity) r v ≠ 1) :
    Fin (portWord r (walk r h (2*r.edges.length+1) [] p).1).length ≃
      ((r.shape h).ComponentEdge ((r.shape h).componentOf p.1) × Bool) :=
  (OrderedDenote.listFiberEquiv _ (portWord_nodup r hd _ (cycle_completion r h hd p hp hu).2.2)
    (fun q => (r.shape h).componentOf q.1 = (r.shape h).componentOf p.1)
    (fun q => (portWord_mem r hd _ q).trans ((covered_iff_vertex_mem r _ q).trans
      ((cycle_vertex_coverage r h hd p hp hu q.1).trans (r.graph_label_eq_iff h q.1 p.1))))).trans
    (componentPortEquiv r h p.1)

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.PortWalk
