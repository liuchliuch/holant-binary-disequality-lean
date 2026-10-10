import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateInterface

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
open Turing Computability BinaryCompose
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

def originalInput (g : Graph) (target : g.Vertex) : Input :=
  ⟨(ReachRound.graphEdges g,(target.val,g.parentTable)),by
    intro row hr
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hr
    exact (ParentOpposite.originalInput g v).property⟩

theorem original_predicate (g : Graph) (target child : g.Vertex) :
    predicate (ReachRound.graphEdges g) target.val (g.parentRow child)=ChildPredicate.value (ChildPredicate.graphInput g target child) := by
  unfold predicate
  have hv : ParentOpposite.Valid (ReachRound.graphEdges g,g.parentRow child) := (ParentOpposite.originalInput g child).property
  rw [dif_pos hv]
  rfl

theorem childrenFrom_zipIdx (edges : List (ℕ × ℕ)) (target i : ℕ) (rows : List Graph.ParentRow) :
    childrenFrom edges target i rows =
      ((rows.zipIdx i).filter (fun p => predicate edges target p.1)).map Prod.snd := by
  induction rows generalizing i with
  | nil => rfl
  | cons row rows ih =>
    cases hp : predicate edges target row <;>
      simp [childrenFrom,List.zipIdx_cons,hp,ih]

theorem parentTable_zipIdx (g : Graph) :
    g.parentTable.zipIdx=(List.finRange g.vertices).map (fun v => (g.parentRow v,v.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [Graph.parentTable,List.get_eq_getElem]

def children (g : Graph) (target : g.Vertex) : List g.Vertex :=
  (List.finRange g.vertices).filter (fun child => ChildPredicate.value (ChildPredicate.graphInput g target child))

/-- Literal increasing original vertex IDs, rather than edge order or an
unordered semantic child set. Each retained row appears once. -/
theorem original_value (g : Graph) (target : g.Vertex) :
    value (originalInput g target)=(children g target).map Fin.val := by
  change childrenFrom (ReachRound.graphEdges g) target.val 0 g.parentTable = _
  rw [childrenFrom_zipIdx,parentTable_zipIdx]
  simp only [List.filter_map,List.map_map,Function.comp_def,original_predicate,children]

theorem mem_children (g : Graph) (target child : g.Vertex) :
    child∈children g target ↔ ChildPredicate.value (ChildPredicate.graphInput g target child)=true := by
  simp [children]
theorem children_nodup (g : Graph) (target : g.Vertex) : (children g target).Nodup :=
  List.Nodup.filter _ (List.nodup_finRange _)
theorem children_length_le (g : Graph) (target : g.Vertex) : (children g target).length≤g.vertices := by
  simpa [children] using List.length_filter_le (fun child => ChildPredicate.value (ChildPredicate.graphInput g target child)) (List.finRange g.vertices)

noncomputable def original_timed (g : Graph) (target : g.Vertex) :
    TM2OutputsInTime (machine actual).computer (inputEncoding.encode (originalInput g target))
      (some (outputEncoding.encode ((children g target).map Fin.val)))
      (timePolynomial.eval (inputEncoding.encode (originalInput g target)).length) := by
  simpa only [original_value] using timed (originalInput g target)
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerate
