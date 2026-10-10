import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ChildEnumerateGraph

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {s b : ℕ} {arity : ℕ → ℕ}

/-- Literal port coefficient and literal reference preserve both original IDs. -/
theorem edge_value (x : Input s b arity) (e : (x.1.1.val.graph x.1.1.property).Edge) (side : Bool)
    (hp : ((x.1.1.val.graph x.1.1.property).parentRow x.2).parent=some (e.val,side))
    (ht : (x.1.1.val.graph x.1.1.property).endpoint e (!side)=x.1.2) :
    value x=portAction s b arity
      (SingletonLabel.label x.1.1.val x.1.1.property
        (x.1.1.val.lookup x.1.1.property (x.1.1.val.graphEdgeEquiv x.1.1.property e,!side)))++Traversal.reference x.2.val := by
  have ee : (x.1.1.val.graphEdgeEquiv x.1.1.property e : Fin x.1.1.val.edges.length)=
      ⟨e.val,(prepared x).property (e.val,side) hp⟩ := Fin.ext rfl
  have lookup : (x.1.1.val.lookup x.1.1.property (x.1.1.val.graphEdgeEquiv x.1.1.property e,!side)).1=x.1.2 := by
    rw [RawClosedNetwork.lookup_vertex,←RawClosedNetwork.graph_endpoint]
    exact ht
  have coefficient : ParentCoefficient.value true (prepared x)=SingletonLabel.label x.1.1.val x.1.1.property
      (x.1.1.val.lookup x.1.1.property (x.1.1.val.graphEdgeEquiv x.1.1.property e,!side)) := by
    unfold ParentCoefficient.value ParentCoefficient.entry
    rw [ParentCoefficient.parent_some true (prepared x) (e.val,side) hp]
    change OrdinaryCoefficient.value ⟨x.1.1,x.1.2,some (⟨e.val,_⟩,!side)⟩=_
    rw [←ee]
    conv_lhs => rw [←lookup]
    exact OrdinaryCoefficient.value_lookup _ _ _
  exact congrArg (fun a => portAction s b arity a++Traversal.reference x.2.val) coefficient

/-- Every ID selected by the actual child scanner has the required original
parent endpoint, so the action chunk never silently uses a foreign vertex. -/
theorem child_value (x : Input s b arity)
    (hc : x.2∈ChildEnumerate.children (x.1.1.val.graph x.1.1.property) x.1.2) :
    ∃ e : (x.1.1.val.graph x.1.1.property).Edge, ∃ side : Bool,
      ((x.1.1.val.graph x.1.1.property).parentRow x.2).parent=some (e.val,side) ∧
      value x=portAction s b arity
        (SingletonLabel.label x.1.1.val x.1.1.property
          (x.1.1.val.lookup x.1.1.property (x.1.1.val.graphEdgeEquiv x.1.1.property e,!side)))++Traversal.reference x.2.val := by
  let g := x.1.1.val.graph x.1.1.property
  have hit := (ChildEnumerate.mem_children g x.1.2 x.2).mp hc
  cases hp : (g.parentRow x.2).parent with
  | none => rw [ChildPredicate.root_false g x.1.2 x.2 hp] at hit; contradiction
  | some q =>
    obtain ⟨e,he,_,_⟩ := g.parentRow_some_spec x.2 q hp
    have hq : (g.parentRow x.2).parent=some (e.val,q.2) := by rw [he]; exact hp
    rw [ChildPredicate.original_edge g x.1.2 x.2 e q.2 hq] at hit
    exact ⟨e,q.2,by rw [he],edge_value x e q.2 hq (of_decide_eq_true hit)⟩
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ActionChild
