import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficientBounds
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.SingletonInterface

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false

theorem value_none (x : RawRootReach.Input s b arity) :
    value ⟨x.1,x.2,none⟩=zeroValue x := by
  unfold value zeroValue
  congr 3

/-- The physical incidence lookup selects the original local port, including
the two different local occurrences of a self-loop. -/
theorem value_lookup (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (q : Fin r.edges.length × Bool) :
    value ⟨⟨r,h⟩,(r.lookup h q).1,some q⟩=SingletonLabel.label r h (r.lookup h q) := by
  simp only [value,SingletonLabel.label_eq,ResidualOptionalSurvivor.selected,ResidualSurvivorQuery.selected,
    ResidualPin.selected,dite_eq_ite,ite_true,Option.map_some,Fin.cast_refl]
  congr 3
  funext j
  simp only [Option.some.injEq]
  exact decide_eq_decide.mpr eq_comm
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OrdinaryCoefficient

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient
open Holant.OneHot.Computable
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

theorem parent_none (flip : Bool) (x : Input s b arity) (hp : x.val.2.parent=none) : parent flip x=none := by
  simp [parent,hp]
theorem parent_some (flip : Bool) (x : Input s b arity) (q : ℕ × Bool) (hp : x.val.2.parent=some q) :
    parent flip x=some (⟨q.1,x.property q hp⟩,side flip q.2) := by
  simp [parent,hp]

theorem root_value (flip : Bool) (x : Input s b arity) (hp : x.val.2.parent=none) :
    value flip x=OrdinaryCoefficient.zeroValue x.val.1 := by
  unfold value entry
  rw [parent_none flip x hp]
  exact OrdinaryCoefficient.value_none _

theorem original_root (x : RawRootReach.Input s b arity)
    (hv : (x.1.val.graph x.1.property).label x.2=x.2) :
    value false (originalInput x)=OrdinaryCoefficient.zeroValue x :=
  root_value false _ ((x.1.val.graph x.1.property).parentRow_none_iff x.2 |>.mpr hv)

/-- The stored child-end bit, rather than an inferred orientation, chooses b.
The return is the same literal original coefficient as the incidence producer. -/
theorem original_nonroot (x : RawRootReach.Input s b arity) (q : ℕ × Bool)
    (hp : ((x.1.val.graph x.1.property).parentRow x.2).parent = some q) :
    let edge : Fin x.1.val.edges.length := ⟨q.1,(originalInput x).property q hp⟩
    value false (originalInput x)=SingletonLabel.label x.1.val x.1.property (x.1.val.lookup x.1.property (edge,q.2)) := by
  dsimp only
  obtain ⟨e,he,endpoint,_⟩ := (x.1.val.graph x.1.property).parentRow_some_spec x.2 q hp
  have ee : x.1.val.graphEdgeEquiv x.1.property e = ⟨q.1,(originalInput x).property q hp⟩ := Fin.ext he
  have lookup : (x.1.val.lookup x.1.property (⟨q.1,(originalInput x).property q hp⟩,q.2)).1=x.2 := by
    rw [RawClosedNetwork.lookup_vertex,←ee,←RawClosedNetwork.graph_endpoint]
    exact endpoint
  unfold value entry
  rw [parent_some false (originalInput x) q hp]
  change OrdinaryCoefficient.value ⟨x.1,x.2,some (⟨q.1,_⟩,q.2)⟩=_
  conv_lhs => rw [←lookup]
  exact OrdinaryCoefficient.value_lookup _ _ _
end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentCoefficient
