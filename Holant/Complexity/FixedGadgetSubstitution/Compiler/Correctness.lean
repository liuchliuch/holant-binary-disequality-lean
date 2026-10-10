import Holant.Complexity.FixedGadgetSubstitution.Compiler.Prefix

/-! Exact ordered-word identities linking the executed index loops to the
recursive Raw.expandRows specification. These are proved identities, not
compiler correctness assumptions. -/
namespace Holant.Complexity.FixedGadgetSubstitution.Compiler
open Computability RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

theorem expandRows_vertices_indexed (templates : ℕ → Template) (offset : ℕ) (rows : List RawVertex) :
    (expandRows templates offset rows).vertices =
      (List.finRange rows.length).flatMap (fun i =>
        (templates (rows.get i).1).placeVertices
          (offset + ((rows.take i.val).map (fun row => (templates row.1).edges.length)).sum)
          (rows.get i).2) := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.length_cons,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
      Function.comp_def,Fin.val_zero,List.take_zero,List.map_nil,List.sum_nil,Nat.add_zero,
      List.get_eq_getElem,List.getElem_cons_zero,Fin.val_succ,List.getElem_cons_succ,
      List.take_succ_cons,List.map_cons,List.sum_cons,expandRows]
    rw [ih]
    simp only [List.get_eq_getElem,Nat.add_assoc]

theorem entries_flatMap {A B : Type} (e : Encoding B Bool) (xs : List A) (f : A → List B) :
    entries e (xs.flatMap f) = xs.flatMap (fun x => entries e (f x)) := by
  simp only [entries,List.flatMap_assoc]

theorem indexed_edges (templates : ℕ → Template) (r : RawClosedNetwork) :
    (List.finRange r.vertices.length).flatMap (fun i => (templates (r.vertices.get i).1).edges) =
      (expandRows templates r.edges.length r.vertices).edges := by
  rw [expandRows_edges]
  have h : (List.finRange r.vertices.length).map r.vertices.get = r.vertices := by
    apply List.ext_getElem <;> simp
  have hh := congrArg (fun xs : List RawVertex => xs.flatMap (fun row => (templates row.1).edges)) h
  simpa only [List.flatMap_map,List.map_map,Function.comp_def,List.flatMap_def] using hh
end Holant.Complexity.FixedGadgetSubstitution.Compiler
