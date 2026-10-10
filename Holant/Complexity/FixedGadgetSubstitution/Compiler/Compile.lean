import Holant.Complexity.FixedGadgetSubstitution.Compiler.Dispatch
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Correctness
import Holant.Complexity.FixedGadgetSubstitution.WellFormed
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! End-to-end fixed-gadget replacement from the original faithful raw network
bytes. All counts, original ordered endpoints, template choice, cumulative
fresh-edge offsets and emitted records are computed inside finite Boolean-stack
programs. The final validation proof changes no byte of either encoding. -/
namespace Holant.Complexity.FixedGadgetSubstitution.Compiler
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (sourceCount b : ℕ) (sourceArity : ℕ → ℕ) (templates : ℕ → Template)

theorem vertexChunks_word (r : Input sourceCount b sourceArity) :
    (List.finRange r.val.vertices.length).flatMap
      (fun v => vertexChunk sourceCount b sourceArity templates ⟨r,v⟩) =
      entries vertexEncoding (replace templates r.val).vertices := by
  rw [replace,expandRows_vertices_indexed,entries_flatMap]
  rfl

noncomputable def replacedVerticesComputes : Computes (validatedEncoding sourceCount b sourceArity)
    (framedListEncoding vertexEncoding) (fun r => (replace templates r.val).vertices) :=
  recode (joinComputes
    (allRowsFlatMapComputes sourceCount b sourceArity _
      (vertexChunkComputes sourceCount b sourceArity templates))
    (constantComputes (validatedEncoding sourceCount b sourceArity) Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun r => by
      change _ ++ [false] = framedListEncode vertexEncoding (replace templates r.val).vertices
      rw [vertexChunks_word]
      simpa only [List.append_nil,framedListEncode,id_eq] using
        entries_append_encode vertexEncoding (replace templates r.val).vertices [])

theorem edgeChunks_word (r : Input sourceCount b sourceArity) :
    (List.finRange r.val.vertices.length).flatMap
      (fun v => entries encodingNatBool (templates (r.val.vertices.get v).1).edges) =
      entries encodingNatBool (expandRows templates r.val.edges.length r.val.vertices).edges := by
  rw [←entries_flatMap,indexed_edges]

noncomputable def replacedEdgesComputes : Computes (validatedEncoding sourceCount b sourceArity)
    (framedListEncoding encodingNatBool) (fun r => (replace templates r.val).edges) :=
  recode (joinComputes
    (joinComputes ((edgesComputes sourceCount b sourceArity).andThen (entriesComputes encodingNatBool))
      (allRowsFlatMapComputes sourceCount b sourceArity _
        (edgeChunkComputes sourceCount b sourceArity templates)))
    (constantComputes (validatedEncoding sourceCount b sourceArity) Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun r => by
      change (entries encodingNatBool r.val.edges ++ _) ++ [false] =
        framedListEncode encodingNatBool (replace templates r.val).edges
      rw [edgeChunks_word]
      simpa only [replace,List.append_nil,framedListEncode,entries,List.flatMap_append,id_eq] using
        entries_append_encode encodingNatBool
          (r.val.edges ++ (expandRows templates r.val.edges.length r.val.vertices).edges) [])

/-- The complete executable compiler already computes the literal raw output;
well-formedness is needed only to refine its result type below. -/
noncomputable def rawComputes : Computes (validatedEncoding sourceCount b sourceArity)
    encoding (fun r => replace templates r.val) :=
  recode (pairComputes (replacedVerticesComputes sourceCount b sourceArity templates)
    (replacedEdgesComputes sourceCount b sourceArity templates)) id (fun _ => rfl) (fun _ => rfl)

variable (s : ℕ) (arity : ℕ → ℕ)
variable (hg : ∀ label < sourceCount, (templates label).WellFormed s b arity ∧
  (templates label).boundary = sourceArity label)

def value (r : Input sourceCount b sourceArity) : Input s b arity :=
  ⟨replace templates r.val,replace_wellFormed templates r.val r.property hg⟩

/-- Unconditional finite-machine compiler from original validated encoding to
target validated encoding; the only premises describe the fixed templates. -/
noncomputable def computes : Computes (validatedEncoding sourceCount b sourceArity)
    (validatedEncoding s b arity) (value sourceCount b sourceArity templates s arity hg) :=
  recode (rawComputes sourceCount b sourceArity templates) id (fun _ => rfl) (fun _ => rfl)

theorem inFP : InFP (validatedEncoding sourceCount b sourceArity)
    (validatedEncoding s b arity) (value sourceCount b sourceArity templates s arity hg) :=
  (computes sourceCount b sourceArity templates s arity hg).inFP

/-- The correction counter is produced from original labels in the same clean
preprocessing computation, ready for the one-query reduction's context tape. -/
noncomputable def withOccurrencesComputes (distinguishedLabel : ℕ) :
    Computes (validatedEncoding sourceCount b sourceArity)
      (pairEncoding (validatedEncoding s b arity) UnaryBinary.unaryEncoding)
      (fun r => (value sourceCount b sourceArity templates s arity hg r,occurrences distinguishedLabel r.val)) :=
  pairComputes (computes sourceCount b sourceArity templates s arity hg)
    (occurrencesComputes sourceCount b sourceArity distinguishedLabel)

/-- Actual elementary Boolean instruction cost, using the same machine and run. -/
theorem primitive_bound (r : Input sourceCount b sourceArity) :
    primitiveCost (computes sourceCount b sourceArity templates s arity hg).machine
      ((computes sourceCount b sourceArity templates s arity hg).outputs r).steps
      (some (initList (computes sourceCount b sourceArity templates s arity hg).machine.computer
        ((validatedEncoding sourceCount b sourceArity).encode r))) ≤
      (primitivePolynomial (computes sourceCount b sourceArity templates s arity hg)).eval
        ((validatedEncoding sourceCount b sourceArity).encode r).length :=
  computes_primitive_cost (computes sourceCount b sourceArity templates s arity hg) r

end Holant.Complexity.FixedGadgetSubstitution.Compiler
