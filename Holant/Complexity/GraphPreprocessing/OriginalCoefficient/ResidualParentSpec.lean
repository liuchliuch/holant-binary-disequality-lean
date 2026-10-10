import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParentData
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonSpec

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParent
open Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.StackProgram.GraphLabelEncoding
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

/-- A root contributes no surviving position. A present parent occupies a
separate original edge occurrence, so the descriptor's fields cannot collide. -/
theorem pin_survivor_disjoint (value side : Bool) (x : Input s b arity) :
    ∀ p ∈ ResidualPin.selected value x.val.1.val x.val.2.1
      (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,side)),
      ∀ q ∈ ResidualOptionalSurvivor.selected (survivorQuery x), p.1 ≠ q := by
  cases hp : x.val.2.2.2 with
  | none => simp [ResidualOptionalSurvivor.selected,survivorQuery,hp]
  | some endpoint =>
    have hne := x.property endpoint (by simp [hp])
    simpa only [ResidualOptionalSurvivor.selected,survivorQuery,hp,ResidualSurvivorQuery.selected] using
      ResidualSingleton.selected_edges_disjoint x.val.1.val x.val.1.property x.val.2.1
        x.val.2.2.1 endpoint.1 hne side endpoint.2 value

def descriptor (a z : Bool) (x : Input s b arity) :
    ResidualLabel.Descriptor (arity (x.val.1.val.vertices.get x.val.2.1).1) :=
  ⟨(ResidualPin.selected a x.val.1.val x.val.2.1 (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,false)),
    ResidualPin.selected z x.val.1.val x.val.2.1 (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,true)),
    ResidualOptionalSurvivor.selected (survivorQuery x)),
    ⟨ResidualPin.selected_ends_disjoint x.val.1.val x.val.1.property x.val.2.2.1 x.val.2.1 a z,
      pin_survivor_disjoint a false x,pin_survivor_disjoint z true x⟩⟩

def descriptorBits (a z : Bool) (x : Input s b arity) : List Bool :=
  (ResidualLabel.descriptorEncoding _).encode (descriptor a z x)

theorem descriptor_word (a z : Bool) (x : Input s b arity) :
    descriptorBits a z x = Holant.Algebraic.frame (ResidualPinQuery.pinBits false a (cutQuery x)) ++
      (Holant.Algebraic.frame (ResidualPinQuery.pinBits true z (cutQuery x)) ++
        ResidualOptionalSurvivor.portBits (survivorQuery x)) := by
  change Holant.Algebraic.frame ((optionEncoding (ResidualLabel.pinEncoding _)).encode
      (ResidualPin.selected a x.val.1.val x.val.2.1 (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,false)))) ++
    (Holant.Algebraic.frame ((optionEncoding (ResidualLabel.pinEncoding _)).encode
      (ResidualPin.selected z x.val.1.val x.val.2.1 (x.val.1.val.lookup x.val.1.property (x.val.2.2.1,true)))) ++
      (optionEncoding (OccurrenceLabel.unaryPortEncoding _)).encode
        (ResidualOptionalSurvivor.selected (survivorQuery x))) = _
  rw [ResidualPin.selected_encode,ResidualPin.selected_encode,ResidualOptionalSurvivor.selected_encode]
  rfl

theorem root_descriptor (a z : Bool) (x : Input s b arity) (h : x.val.2.2.2=none) :
    descriptor a z x = ResidualPin.zeroDescriptor x.val.1.val x.val.1.property x.val.2.2.1 x.val.2.1 a z := by
  apply Subtype.ext
  simp only [descriptor,ResidualPin.zeroDescriptor,ResidualOptionalSurvivor.selected,survivorQuery,h]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParent
