import Holant.Complexity.EdgeSubdivision.Records
import Holant.Complexity.FixedFieldMachines.PrimitiveCost

/-! Polynomial Boolean-machine edge subdivision. Every count and edge label is
parsed from the original graph. Well-formedness refines the output type without
changing either the input bytes or the emitted graph bytes. -/
namespace Holant.Complexity.EdgeSubdivision.Compiler
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork
open Holant.OneHot.StackProgram.GraphLabelEncoding
open FixedGadgetSubstitution.Compiler
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s b : ℕ) (arity : ℕ → ℕ)

theorem edgeRows_eq (r : Input s b arity) :
    (List.finRange r.val.edges.length).map (fun e => edgeRow s b arity ⟨r,e⟩) =
      edgeVertices s r.val.edges := by
  apply List.ext_getElem <;> simp [edgeVertices,edgeRow]

theorem edgeRows_word (r : Input s b arity) :
    (List.finRange r.val.edges.length).flatMap
      (fun e => entry vertexEncoding (edgeRow s b arity ⟨r,e⟩)) =
      entries vertexEncoding (edgeVertices s r.val.edges) := by
  rw [←edgeRows_eq s b arity r]
  simp only [entries,List.flatMap_map,Function.comp_def]

noncomputable def verticesComputes : Computes (validatedEncoding s b arity)
    (framedListEncoding vertexEncoding) (fun r => (subdivide s r.val).vertices) :=
  recode (joinComputes
    (joinComputes
      (((rowsComputes s b arity).andThen
        (mapComputes vertexEncoding vertexEncoding oldVertex oldVertexComputes)).andThen
          (entriesComputes vertexEncoding))
      (allEdgesFlatMapComputes s b arity _
        ((edgeRowComputes s b arity).andThen (entryComputes vertexEncoding))))
    (constantComputes (validatedEncoding s b arity) Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun r => by
      change (entries vertexEncoding (r.val.vertices.map oldVertex) ++ _) ++ [false] =
        framedListEncode vertexEncoding (subdivide s r.val).vertices
      simp only [Function.comp_def,id_eq]
      rw [edgeRows_word]
      simpa only [subdivide,entries,List.flatMap_append,List.append_nil,framedListEncode,
        id_eq] using entries_append_encode vertexEncoding
          (r.val.vertices.map oldVertex ++ edgeVertices s r.val.edges) [])

theorem doubleZeros {A : Type} (xs : List A) :
    xs.flatMap (fun _ => ([0,0] : List ℕ)) = List.replicate (2*xs.length) 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_cons,Nat.mul_add,Nat.mul_one,ih]
    rw [Nat.add_comm, List.replicate_add]
    rfl

theorem edgeLabels_word (r : Input s b arity) :
    (List.finRange r.val.edges.length).flatMap
      (fun _ => entries encodingNatBool [0,0]) =
      entries encodingNatBool (subdivide s r.val).edges := by
  have h := doubleZeros (List.finRange r.val.edges.length)
  simp only [List.length_finRange] at h
  rw [subdivide,←h]
  simp only [entries,List.flatMap_assoc]

noncomputable def targetEdgesComputes : Computes (validatedEncoding s b arity)
    (framedListEncoding encodingNatBool) (fun r => (subdivide s r.val).edges) :=
  recode (joinComputes
    (allEdgesFlatMapComputes s b arity _
      (constantComputes (edgeQueryEncoding s b arity) Frame.wordEncoding
        (entries encodingNatBool [0,0])))
    (constantComputes (validatedEncoding s b arity) Frame.wordEncoding [false]))
    id (fun _ => rfl) (fun r => by
      change _ ++ [false] = framedListEncode encodingNatBool (subdivide s r.val).edges
      rw [edgeLabels_word]
      simpa only [List.append_nil,framedListEncode,id_eq] using
        entries_append_encode encodingNatBool (subdivide s r.val).edges [])

noncomputable def rawComputes : Computes (validatedEncoding s b arity)
    encoding (fun r => subdivide s r.val) :=
  recode (pairComputes (verticesComputes s b arity) (targetEdgesComputes s b arity))
    id (fun _ => rfl) (fun _ => rfl)

def value (r : Input s b arity) : Input (s+b) 1 (targetArity s arity) :=
  ⟨subdivide s r.val,subdivide_wellFormed s b arity r.val r.property⟩

noncomputable def computes : Computes (validatedEncoding s b arity)
    (validatedEncoding (s+b) 1 (targetArity s arity)) (value s b arity) :=
  recode (rawComputes s b arity) id (fun _ => rfl) (fun _ => rfl)

theorem inFP : InFP (validatedEncoding s b arity)
    (validatedEncoding (s+b) 1 (targetArity s arity)) (value s b arity) :=
  (computes s b arity).inFP

theorem primitive_bound (r : Input s b arity) :
    primitiveCost (computes s b arity).machine
      ((computes s b arity).outputs r).steps
      (some (initList (computes s b arity).machine.computer
        ((validatedEncoding s b arity).encode r))) ≤
      (primitivePolynomial (computes s b arity)).eval
        ((validatedEncoding s b arity).encode r).length :=
  computes_primitive_cost (computes s b arity) r

end Holant.Complexity.EdgeSubdivision.Compiler
