import Holant.Complexity.EdgeSubdivision.Combinators
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Records

/-! Actual parsing and iteration over all original edge labels. The input
contains only the validated raw graph, with no supplied counts or offsets. -/
namespace Holant.Complexity.EdgeSubdivision.Compiler
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
open FixedGadgetSubstitution.Compiler
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev EdgeQuery (s b : ℕ) (arity : ℕ → ℕ) :=
  Σ r : Input s b arity, Fin r.val.edges.length

def edgeQueryEncoding (s b : ℕ) (arity : ℕ → ℕ) :=
  sigmaEncoding (validatedEncoding s b arity)
    (fun r => OccurrenceLabel.unaryPortEncoding r.val.edges.length)

variable (s b : ℕ) (arity : ℕ → ℕ)

noncomputable def edgeSourceComputes : Computes (edgeQueryEncoding s b arity)
    (validatedEncoding s b arity) (fun x => x.1) :=
  recode (Wiring.firstComputes (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

noncomputable def edgeIndexComputes : Computes (edgeQueryEncoding s b arity)
    UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

noncomputable def originalEdgeComputes : Computes (edgeQueryEncoding s b arity)
    encodingNatBool (fun x => x.1.val.edges.get x.2) := by
  let prepare : Computes (edgeQueryEncoding s b arity)
      (ParentRowSelect.inputEncoding encodingNatBool)
      (fun x => ⟨x.1.val.edges,x.2⟩) :=
    recode (pairComputes
      ((edgeSourceComputes s b arity).andThen (edgesComputes s b arity))
      (edgeIndexComputes s b arity)) id (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ParentRowSelect.computes encodingNatBool)

def edgeRow (x : EdgeQuery s b arity) : RawVertex :=
  (s+x.1.val.edges.get x.2,inside x.2.val)

noncomputable def edgeRowComputes : Computes (edgeQueryEncoding s b arity)
    vertexEncoding (edgeRow s b arity) :=
  recode (pairComputes
    ((pairComputes (constantComputes (edgeQueryEncoding s b arity) encodingNatBool s)
      (originalEdgeComputes s b arity)).andThen
        FixedGadgetSubstitution.Compiler.addComputes)
    (((edgeIndexComputes s b arity).andThen UnaryBinary.computes).andThen insideComputes))
    id (fun _ => rfl) (fun _ => rfl)

def allEdgeQueriesEncoding := ContextFlatMap.inputEncoding (validatedEncoding s b arity)
  (fun r => OccurrenceLabel.unaryPortEncoding r.val.edges.length)

noncomputable def allEdgeQueriesComputes : Computes (validatedEncoding s b arity)
    (allEdgeQueriesEncoding s b arity)
    (fun r => ⟨r,List.finRange r.val.edges.length⟩) :=
  recode (pairComputes (identityComputes (validatedEncoding s b arity))
    ((edgeCountComputes s b arity).andThen ComponentSelection.UnaryRange.computes))
    id (fun _ => rfl) (fun r => by
      change Holant.Algebraic.frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
      rw [←finRange_values,finListEncoding]
      rfl)

noncomputable def allEdgesFlatMapComputes (f : EdgeQuery s b arity → List Bool)
    (w : Computes (edgeQueryEncoding s b arity) Frame.wordEncoding f) :
    Computes (validatedEncoding s b arity) Frame.wordEncoding
      (fun r => (List.finRange r.val.edges.length).flatMap (fun e => f ⟨r,e⟩)) :=
  (allEdgeQueriesComputes s b arity).andThen
    (ContextFlatMap.computes (validatedEncoding s b arity)
      (fun r => OccurrenceLabel.unaryPortEncoding r.val.edges.length) f w)

end Holant.Complexity.EdgeSubdivision.Compiler
