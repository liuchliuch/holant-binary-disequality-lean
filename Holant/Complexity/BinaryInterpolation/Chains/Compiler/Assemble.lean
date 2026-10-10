import Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! Whole-input Boolean compilation of positive chain queries. The program
reads the original raw graph and unary k, visits every original occurrence,
emits k+1 actual B rows at marked occurrences, retains other rows, and appends
exactly k native-edge labels per marked occurrence. No expanded graph is input.
-/
namespace Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution RawClosedNetwork
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

variable (s b : ℕ) (arity : ℕ → ℕ)

def queriesEncoding := ContextFlatMap.inputEncoding (inputEncoding s b arity)
  (fun x => OccurrenceLabel.unaryPortEncoding x.2.val.vertices.length)

noncomputable def queriesComputes : Computes (inputEncoding s b arity)
    (queriesEncoding s b arity) (fun x => ⟨x,List.finRange x.2.val.vertices.length⟩) :=
  recode (pairComputes (identityComputes (inputEncoding s b arity))
    (((Wiring.secondComputes UnaryBinary.unaryEncoding (validatedEncoding s b arity)).andThen
      (FixedGadgetSubstitution.Compiler.vertexCountComputes s b arity)).andThen
        ComponentSelection.UnaryRange.computes)) id (fun _ => rfl) (fun x => by
      change Holant.Algebraic.frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
      rw [←FixedGadgetSubstitution.Compiler.finRange_values,
        FixedGadgetSubstitution.Compiler.finListEncoding]
      rfl)

noncomputable def allRowsComputes (f : Query s b arity → List Bool)
    (w : Computes (queryEncoding s b arity) Frame.wordEncoding f) :
    Computes (inputEncoding s b arity) Frame.wordEncoding
      (fun x => (List.finRange x.2.val.vertices.length).flatMap (fun i => f ⟨x,i⟩)) :=
  (queriesComputes s b arity).andThen
    (ContextFlatMap.computes (inputEncoding s b arity)
      (fun x => OccurrenceLabel.unaryPortEncoding x.2.val.vertices.length) f w)

noncomputable def repeatEdgesComputes (edge : ℕ) : Computes UnaryBinary.unaryEncoding
    (framedListEncoding encodingNatBool) (fun k => List.replicate k edge) := by
  let ea := pairEncoding Frame.wordEncoding UnaryBinary.unaryEncoding
  let provider : Computes ea encodingNatBool (fun _ => edge) :=
    constantComputes ea encodingNatBool edge
  let prepare := pairComputes
    (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding []) ComponentSelection.UnaryRange.computes
  exact congrComputes (prepare.andThen (mapListComputes Frame.wordEncoding UnaryBinary.unaryEncoding
    encodingNatBool (fun _ _ => edge) provider)) (fun k => by simp)

def edgeRows (distinguished edge : ℕ) (x : Query s b arity) : List ℕ :=
  if marked s b arity distinguished x then List.replicate x.1.1 edge else []

noncomputable def edgeChunkComputes (distinguished edge : ℕ) :
    Computes (queryEncoding s b arity) Frame.wordEncoding
      (fun x => FixedGadgetSubstitution.Compiler.entries encodingNatBool
        (edgeRows s b arity distinguished edge x)) := by
  let yes := ((lengthComputes s b arity).andThen (repeatEdgesComputes edge)).andThen
    (FixedGadgetSubstitution.Compiler.entriesComputes encodingNatBool)
  let no := constantComputes (queryEncoding s b arity) Frame.wordEncoding []
  refine congrComputes (ifComputes (markedComputes s b arity distinguished) yes no) ?_
  intro x
  cases h : marked s b arity distinguished x <;>
    simp [edgeRows,h,FixedGadgetSubstitution.Compiler.entries]

def vertices (distinguished label : ℕ) (x : Input s b arity) : List RawVertex :=
  (List.finRange x.2.val.vertices.length).flatMap
    (fun i => rows s b arity distinguished label ⟨x,i⟩)

def edges (distinguished edge : ℕ) (x : Input s b arity) : List ℕ :=
  x.2.val.edges ++ (List.finRange x.2.val.vertices.length).flatMap
    (fun i => edgeRows s b arity distinguished edge ⟨x,i⟩)

noncomputable def verticesComputes (distinguished label : ℕ) : Computes (inputEncoding s b arity)
    (framedListEncoding vertexEncoding) (vertices s b arity distinguished label) := by
  let run := allRowsComputes s b arity _ (rowChunkComputes s b arity distinguished label)
  refine recode (FixedGadgetSubstitution.Compiler.joinComputes run
    (constantComputes (inputEncoding s b arity) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro x
  have h := FixedGadgetSubstitution.Compiler.entries_append_encode vertexEncoding
    (vertices s b arity distinguished label x) []
  simpa only [vertices,FixedGadgetSubstitution.Compiler.entries,List.flatMap_assoc,
    List.append_nil,framedListEncode,framedListEncoding,Frame.wordEncoding,id_eq,Function.comp_def] using h

noncomputable def edgesComputes (distinguished edge : ℕ) : Computes (inputEncoding s b arity)
    (framedListEncoding encodingNatBool) (edges s b arity distinguished edge) := by
  let original := (((Wiring.secondComputes UnaryBinary.unaryEncoding (validatedEncoding s b arity)).andThen
    (FixedGadgetSubstitution.Compiler.edgesComputes s b arity)).andThen
      (FixedGadgetSubstitution.Compiler.entriesComputes encodingNatBool))
  let added := allRowsComputes s b arity _ (edgeChunkComputes s b arity distinguished edge)
  refine recode (FixedGadgetSubstitution.Compiler.joinComputes
    (FixedGadgetSubstitution.Compiler.joinComputes original added)
    (constantComputes (inputEncoding s b arity) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro x
  have h := FixedGadgetSubstitution.Compiler.entries_append_encode encodingNatBool
    (edges s b arity distinguished edge x) []
  simpa only [edges,FixedGadgetSubstitution.Compiler.entries,List.flatMap_assoc,List.flatMap_append,
    List.append_nil,framedListEncode,framedListEncoding,Frame.wordEncoding,id_eq,Function.comp_def] using h

def raw (distinguished label edge : ℕ) (x : Input s b arity) : RawClosedNetwork :=
  ⟨vertices s b arity distinguished label x, edges s b arity distinguished edge x⟩

/-- One fixed finite program accepts the original graph and a variable unary k.
Its actual primitive Boolean cost is polynomial in those original input bytes. -/
noncomputable def rawComputes (distinguished label edge : ℕ) :
    Computes (inputEncoding s b arity) encoding (raw s b arity distinguished label edge) :=
  recode (pairComputes (verticesComputes s b arity distinguished label)
    (edgesComputes s b arity distinguished edge)) id (fun _ => rfl) (fun _ => rfl)

theorem raw_inFP (distinguished label edge : ℕ) :
    InFP (inputEncoding s b arity) encoding (raw s b arity distinguished label edge) :=
  (rawComputes s b arity distinguished label edge).inFP

theorem primitive_bound (distinguished label edge : ℕ) (x : Input s b arity) :
    primitiveCost (rawComputes s b arity distinguished label edge).machine
      ((rawComputes s b arity distinguished label edge).outputs x).steps
      (some (initList (rawComputes s b arity distinguished label edge).machine.computer
        ((inputEncoding s b arity).encode x))) ≤
      (primitivePolynomial (rawComputes s b arity distinguished label edge)).eval
        ((inputEncoding s b arity).encode x).length :=
  computes_primitive_cost (rawComputes s b arity distinguished label edge) x

end Holant.Complexity.BinaryInterpolation.Chains.Compiler.Occurrence
