import Holant.Proofs.Tractability.ProductMachine.Templates
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.EdgeWord


namespace Holant.LocalDrafts.Tractability.ProductMachine.RawCompiler

open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
open Templates (LocalFactor Record recordEncoding)

variable (s b : ℕ) (arity : ℕ → ℕ)
abbrev EdgeQuery := EdgeWord.Input s b arity
abbrev edgeEncoding := EdgeWord.inputEncoding s b arity

noncomputable def source : Computes (edgeEncoding s b arity)
    (RawClosedNetwork.validatedEncoding s b arity) (fun x => x.1) :=
  recode (Wiring.firstComputes (RawClosedNetwork.validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1, x.2.val)) (fun _ => rfl) (fun _ => rfl)

noncomputable def index : Computes (edgeEncoding s b arity) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (RawClosedNetwork.validatedEncoding s b arity) UnaryBinary.unaryEncoding)
    (fun x => (x.1, x.2.val)) (fun _ => rfl) (fun _ => rfl)

def edgeLabel (x : EdgeQuery s b arity) : Fin b := x.1.val.edgeLabel x.1.property x.2

noncomputable def labelComputes : Computes (edgeEncoding s b arity)
    (SignatureLabel.binaryFinEncoding b) (edgeLabel s b arity) := by
  let prepare : Computes (edgeEncoding s b arity) (ParentRowSelect.inputEncoding encodingNatBool)
      (fun x => ⟨x.1.val.edges, x.2⟩) :=
    recode (pairComputes ((source s b arity).andThen (edgesComputes s b arity))
      (index s b arity)) id (fun _ => rfl) (fun _ => rfl)
  exact recode (prepare.andThen (ParentRowSelect.computes encodingNatBool)) id
    (fun _ => rfl) (fun _ => rfl)

noncomputable def portsComputes : Computes (edgeEncoding s b arity) Templates.portsEncoding
    (fun x => [(x.2.val, false), (x.2.val, true)]) :=
  congrComputes (fixedListComputes (edgeEncoding s b arity) RawClosedNetwork.endpointEncoding
    (fun x side => (x.2.val, side))
    (fun side => ((index s b arity).andThen UnaryBinary.computes).andThen (EndpointQuery.computes side))
    [false, true]) (fun _ => rfl)

variable (vertices : Fin s → List LocalFactor) (edges : Fin b → List LocalFactor)

def edgeEntries (x : EdgeQuery s b arity) : List Bool :=
  entries recordEncoding ((edges (edgeLabel s b arity x)).map
    (Templates.place [(x.2.val, false), (x.2.val, true)]))

noncomputable def edgeComputes : Computes (edgeEncoding s b arity) Frame.wordEncoding
    (edgeEntries s b arity edges) :=
  chooseComputes (edgeEncoding s b arity) Frame.wordEncoding b (edgeLabel s b arity)
    (fun x i => entries recordEncoding ((edges i).map
      (Templates.place [(x.2.val, false), (x.2.val, true)])))
    ((labelComputes s b arity).andThen
      (FiniteRecode.computes (SignatureLabel.binaryFinEncoding b) UnaryBinary.unaryEncoding
        Fin.val b.size (SignatureLabel.binaryFinEncoding_length_le b)))
    (fun i => (portsComputes s b arity).andThen (Templates.templateEntriesComputes (edges i)))

noncomputable def allEdgesPrepare : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (ContextFlatMap.inputEncoding (RawClosedNetwork.validatedEncoding s b arity)
      (fun r => OccurrenceLabel.unaryPortEncoding r.val.edges.length))
    (fun r => ⟨r, List.finRange r.val.edges.length⟩) :=
  recode (pairComputes (identityComputes (RawClosedNetwork.validatedEncoding s b arity))
    ((edgeCountComputes s b arity).andThen ComponentSelection.UnaryRange.computes))
    id (fun _ => rfl) (fun r => by
      change Holant.Algebraic.frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _) = _
      rw [← finRange_values, finListEncoding]
      rfl)

def allEdgeEntries (r : Input s b arity) : List Bool :=
  (List.finRange r.val.edges.length).flatMap (fun e => edgeEntries s b arity edges ⟨r, e⟩)

noncomputable def allEdgesComputes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    Frame.wordEncoding (allEdgeEntries s b arity edges) :=
  (allEdgesPrepare s b arity).andThen
    (ContextFlatMap.computes (RawClosedNetwork.validatedEncoding s b arity)
      (fun r => OccurrenceLabel.unaryPortEncoding r.val.edges.length)
      (edgeEntries s b arity edges) (edgeComputes s b arity edges))

def factors (r : Input s b arity) : List Record :=
  (List.finRange r.val.vertices.length).flatMap (fun v =>
    (vertices (sourceLabel s b arity ⟨r, v⟩)).map (Templates.place (r.val.vertices.get v).2)) ++
  (List.finRange r.val.edges.length).flatMap (fun e =>
    (edges (edgeLabel s b arity ⟨r, e⟩)).map (Templates.place [(e.val, false), (e.val, true)]))

theorem entries_flatMap {I : Type} (xs : List I) (f : I → List Record) :
    entries recordEncoding (xs.flatMap f) = xs.flatMap (fun i => entries recordEncoding (f i)) := by
  simp [entries, List.flatMap_assoc]

/-- Clean complete framed record stream, with exactly one final terminator. -/
noncomputable def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    (framedListEncoding recordEncoding) (factors s b arity vertices edges) := by
  let chunks := joinComputes (Templates.allVerticesComputes s b arity vertices)
    (allEdgesComputes s b arity edges)
  refine recode (joinComputes chunks
    (constantComputes (RawClosedNetwork.validatedEncoding s b arity) Frame.wordEncoding [false]))
    id (fun _ => rfl) ?_
  intro r
  have h := entries_append_encode recordEncoding (factors s b arity vertices edges r) []
  simpa [factors, entries_flatMap, Templates.allVertexEntries, Templates.vertexEntries,
    allEdgeEntries, edgeEntries, entries, List.flatMap_append, List.append_assoc,
    framedListEncoding, framedListEncode, Frame.wordEncoding, List.flatMap_assoc] using h

theorem primitive_bound (r : Input s b arity) :
    let w := computes s b arity vertices edges
    primitiveCost w.machine (w.outputs r).steps
      (some (Turing.initList w.machine.computer (RawClosedNetwork.encoding.encode r.val))) ≤
      (primitivePolynomial w).eval (RawClosedNetwork.encoding.encode r.val).length :=
  computes_primitive_cost (computes s b arity vertices edges) r

end Holant.LocalDrafts.Tractability.ProductMachine.RawCompiler
