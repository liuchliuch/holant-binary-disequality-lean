import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonData
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualOriginalAssignment

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
open Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

private theorem ports_eq (r : RawClosedNetwork) (p q : r.Ports arity)
    (hv : p.1=q.1) (hi : p.2.val=q.2.val) : p=q := by
  rcases p with ⟨v,i⟩
  rcases q with ⟨w,j⟩
  dsimp only at hv hi
  cases hv
  have he : i=j := Fin.ext hi
  cases he
  rfl

/-- A surviving endpoint from another original edge cannot collide with either
removed-edge pin. This includes loops, parallel edges and swapped local ports. -/
theorem selected_edges_disjoint (r : RawClosedNetwork) (h : r.WellFormed s b arity)
    (v : Fin r.vertices.length) (cut parent : Fin r.edges.length) (hne : cut ≠ parent)
    (cutSide parentSide value : Bool) :
    ∀ p ∈ ResidualPin.selected value r v (r.lookup h (cut,cutSide)),
      ∀ q ∈ (ResidualPin.selected true r v (r.lookup h (parent,parentSide))).map Prod.fst,
        p.1 ≠ q := by
  intro p hp q hq he
  obtain ⟨q',hq',hval⟩ := Option.mem_map.mp hq
  obtain ⟨hv,hpval,_⟩ := ResidualPin.selected_some value r v _ p hp
  obtain ⟨hw,hqval,_⟩ := ResidualPin.selected_some true r v _ q' hq'
  have hi : (r.lookup h (cut,cutSide)).2.val = (r.lookup h (parent,parentSide)).2.val :=
    hpval.trans ((congrArg Fin.val (he.trans hval.symm)).trans hqval.symm)
  have heq := congrArg (r.route h) (ports_eq r _ _ (hv.trans hw.symm) hi)
  rw [r.route_lookup h (cut,cutSide),r.route_lookup h (parent,parentSide)] at heq
  exact hne (congrArg Prod.fst heq)

/-- All three fields are derived from original incidences; no local pin or
local surviving position is supplied as an input. -/
def descriptor (a z : Bool) (x : Input s b arity) :
    ResidualLabel.Descriptor (arity (x.val.1.val.vertices.get x.val.2.1).1) :=
  ⟨(ResidualPin.selected a x.val.1.val x.val.2.1 (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,false)),
    ResidualPin.selected z x.val.1.val x.val.2.1 (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,true)),
    ResidualSurvivorQuery.selected (survivorQuery x)),
    ⟨ResidualPin.selected_ends_disjoint x.val.1.val x.val.1.property x.val.2.2.1 x.val.2.1 a z,
     selected_edges_disjoint x.val.1.val x.val.1.property x.val.2.1 x.val.2.2.1 x.val.2.2.2.1 x.property false x.val.2.2.2.2 a,
     selected_edges_disjoint x.val.1.val x.val.1.property x.val.2.1 x.val.2.2.1 x.val.2.2.2.1 x.property true x.val.2.2.2.2 z⟩⟩

def descriptorBits (a z : Bool) (x : Input s b arity) : List Bool :=
  (ResidualLabel.descriptorEncoding _).encode (descriptor a z x)

theorem descriptor_word (a z : Bool) (x : Input s b arity) :
    descriptorBits a z x = Holant.Algebraic.frame (ResidualPinQuery.pinBits false a (cutQuery x)) ++
      (Holant.Algebraic.frame (ResidualPinQuery.pinBits true z (cutQuery x)) ++
        ResidualSurvivorQuery.portBits (survivorQuery x)) := by
  change Holant.Algebraic.frame ((optionEncoding (ResidualLabel.pinEncoding _)).encode
      (ResidualPin.selected a x.val.1.val x.val.2.1 (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,false)))) ++
    (Holant.Algebraic.frame ((optionEncoding (ResidualLabel.pinEncoding _)).encode
      (ResidualPin.selected z x.val.1.val x.val.2.1 (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,true)))) ++
      (optionEncoding (OccurrenceLabel.unaryPortEncoding _)).encode
        (ResidualSurvivorQuery.selected (survivorQuery x))) = _
  rw [ResidualPin.selected_encode,ResidualPin.selected_encode,ResidualSurvivorQuery.selected_encode]
  rfl

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingleton
