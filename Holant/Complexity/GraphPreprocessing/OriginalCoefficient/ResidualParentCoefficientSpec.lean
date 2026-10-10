import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParentCoefficient
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualZeroCoefficientSpec
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualSingletonCoefficientSpec

/-! Literal conditioned-label identity for the one physical optional-parent
pipeline, specializing to original root-zero and surviving-singleton cases. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParentCoefficient
open Computability
variable {s b : ℕ} {arity : ℕ → ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

def singletonInput (x : Input (s := s) (b := b) (arity := arity))
    (q : Fin x.val.1.val.edges.length × Bool) (h : x.val.2.2.2=some q) : ResidualSingleton.Input s b arity :=
  ⟨⟨x.val.1,x.val.2.1,x.val.2.2.1,q⟩,x.property q (by simp [h])⟩

theorem descriptor_some (a z : Bool) (x : Input (s := s) (b := b) (arity := arity))
    (q : Fin x.val.1.val.edges.length × Bool) (h : x.val.2.2.2=some q) :
    ResidualParent.descriptor a z x = ResidualSingleton.descriptor a z (singletonInput x q h) := by
  apply Subtype.ext
  simp only [ResidualParent.descriptor,ResidualSingleton.descriptor,singletonInput,
    ResidualOptionalSurvivor.selected,ResidualParent.survivorQuery,h,ResidualSingleton.survivorQuery]

theorem literal_root (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) (h : x.val.2.2.2=none) :
    literal a z x = ResidualZeroCoefficient.literal a z (ResidualParent.cutQuery x) := by
  change ResidualVertex.label x.val.1.val x.val.1.property x.val.2.1 (ResidualParent.descriptor a z x) = _
  rw [ResidualParent.root_descriptor a z x h]
  rfl

theorem literal_some (a z : Bool) (x : Input (s := s) (b := b) (arity := arity))
    (q : Fin x.val.1.val.edges.length × Bool) (h : x.val.2.2.2=some q) :
    literal a z x = ResidualSingletonCoefficient.literal a z (singletonInput x q h) := by
  change ResidualVertex.label x.val.1.val x.val.1.property x.val.2.1 (ResidualParent.descriptor a z x) = _
  rw [descriptor_some a z x q h]
  rfl

/-- The optional original endpoint determines zero or one surviving original
occurrence in the conditioned graph's increasing local-port enumeration. -/
def survivingWord (x : Input (s := s) (b := b) (arity := arity)) :
    Fin (((x.val.1.val.labelNetwork x.val.1.property).asFinite).executableRemainingPorts x.val.2.2.1 x.val.2.1).card → Bool :=
  fun i => decide (x.val.2.2.2 = some (x.val.1.val.route x.val.1.property ⟨x.val.2.1,
    (((x.val.1.val.labelNetwork x.val.1.property).asFinite).executableRemainingPortEquiv
      x.val.2.2.1 x.val.2.1 i).val⟩))

theorem literal_eq_conditioned (a z : Bool) (x : Input (s := s) (b := b) (arity := arity)) :
    literal a z x =
      (((x.val.1.val.labelNetwork x.val.1.property).asFinite).executableConditionEdge x.val.2.2.1 a z).vertex
        x.val.2.1 (survivingWord x) := by
  cases hp : x.val.2.2.2 with
  | none =>
    rw [literal_root a z x hp,ResidualZeroCoefficient.literal_eq_conditioned_zero]
    congr 1
    funext i
    simp [survivingWord,hp]
  | some q =>
    rw [literal_some a z x q hp,ResidualSingletonCoefficient.literal_eq_conditioned]
    congr 1
    funext i
    simp [ResidualSingletonCoefficient.survivingWord,survivingWord,singletonInput,hp,eq_comm]

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ResidualParentCoefficient
