import Holant.Proofs.BinaryInterpolation.SingularExtraction.RawDisjoint
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.UnionMachine
open Holant.Complexity Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution FixedGadgetSubstitution.Compiler RawClosedNetwork
variable (s b : ℕ) (arity : ℕ → ℕ)
set_option backward.isDefEq.respectTransparency false

def anchorTemplate (t : RawClosedNetwork) : Template :=
  ⟨0, t.vertices.map (fun row => (row.1,row.2.map Sum.inr)), t.edges⟩

theorem place_anchor (t : RawClosedNetwork) (m : ℕ) :
    (anchorTemplate t).placeVertices m [] = t.vertices.map (RawDisjoint.shiftRow m) := by
  simp [anchorTemplate, Template.placeVertices, Template.placeEndpoint,
    RawDisjoint.shiftRow, RawDisjoint.shiftEndpoint, List.map_map, Function.comp_def]

def shiftedRowsComputes (t : RawClosedNetwork) :
    Computes (validatedEncoding s b arity) (framedListEncoding vertexEncoding)
      (fun r => t.vertices.map (RawDisjoint.shiftRow r.val.edges.length)) := by
  let pre : Computes (validatedEncoding s b arity) placementEncoding
      (fun r => (r.val.edges.length,[])) :=
    pairComputes ((edgeCountComputes s b arity).andThen UnaryBinary.computes)
      (constantComputes _ (framedListEncoding endpointEncoding) [])
  exact congrComputes (pre.andThen (templateComputes (anchorTemplate t)))
    (fun r => place_anchor t r.val.edges.length)

def rowsComputes (t : RawClosedNetwork) :
    Computes (validatedEncoding s b arity) (framedListEncoding vertexEncoding)
      (fun r => (RawDisjoint.union r.val t).vertices) :=
  recode (joinComputes
    ((Compiler.rowsComputes s b arity).andThen (entriesComputes vertexEncoding))
    ((shiftedRowsComputes s b arity t).andThen (encodeComputes (framedListEncoding vertexEncoding))))
    id (fun _ => rfl) (fun r => entries_append_encode vertexEncoding _ _)

def rawComputes (t : RawClosedNetwork) : Computes (validatedEncoding s b arity) encoding
    (fun r => RawDisjoint.union r.val t) :=
  recode (pairComputes (rowsComputes s b arity t)
    ((Compiler.edgesComputes s b arity).andThen (appendComputes encodingNatBool t.edges)))
    id (fun _ => rfl) (fun _ => rfl)

def value (t : Input s b arity) (r : Input s b arity) : Input s b arity :=
  ⟨RawDisjoint.union r.val t.val, RawDisjoint.union_wellFormed r.property t.property⟩

def computes (t : Input s b arity) : Computes (validatedEncoding s b arity)
    (validatedEncoding s b arity) (value s b arity t) :=
  recode (rawComputes s b arity t.val) id (fun _ => rfl) (fun _ => rfl)

theorem primitive_bound (t r : Input s b arity) :
    primitiveCost (computes s b arity t).machine ((computes s b arity t).outputs r).steps
      (some (Turing.initList (computes s b arity t).machine.computer
        ((validatedEncoding s b arity).encode r))) ≤
      (primitivePolynomial (computes s b arity t)).eval ((validatedEncoding s b arity).encode r).length :=
  computes_primitive_cost (computes s b arity t) r

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.UnionMachine
