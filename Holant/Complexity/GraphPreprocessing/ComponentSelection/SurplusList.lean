import Holant.Complexity.GraphPreprocessing.ComponentSelection.EndpointPredicate
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.WordJoin

/-! The preserved original edge/parent-table context drives one physical
endpoint predicate for each actual edge ID. Selected unary entries are emitted
in the supplied order and finished with the canonical list terminator. -/
namespace Holant.Complexity.GraphPreprocessing.ComponentSelection.SurplusList
open Turing Computability BinaryCompose FixedFieldMachines OriginalCoefficient
open Holant.OneHot.Computable Holant.OneHot.StackProgram.GraphLabelEncoding
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

def chunk (x : EndpointPredicate.Input) : List Bool :=
  if EndpointPredicate.value x then true::Holant.Algebraic.frame (List.replicate x.2.val true) else []
noncomputable def indexWordComputes : Computes EndpointPredicate.inputEncoding Frame.wordEncoding
    (fun x => List.replicate x.2.val true) :=
  recode EndpointPredicate.indexComputes id (fun _ => rfl) (fun _ => rfl)
noncomputable def chunkComputes : Computes EndpointPredicate.inputEncoding Frame.wordEncoding chunk :=
  (pairComputes EndpointPredicate.computes indexWordComputes).andThen SelectedEntry.computes
abbrev Input := Σ c : EndpointPredicate.Context, List (Fin c.val.1.1.length)
def indices (c : EndpointPredicate.Context) := OccurrenceLabel.unaryPortEncoding c.val.1.1.length
def inputEncoding := ContextFlatMap.inputEncoding EndpointPredicate.contextEncoding indices
abbrev outputEncoding := framedListEncoding UnaryBinary.unaryEncoding
def value (x : Input) : List ℕ := (x.2.filter fun e => EndpointPredicate.value ⟨x.1,e⟩).map Fin.val
noncomputable def chunksComputes : Computes inputEncoding Frame.wordEncoding
    (fun x => x.2.flatMap fun e => chunk ⟨x.1,e⟩) :=
  ContextFlatMap.computes EndpointPredicate.contextEncoding indices chunk chunkComputes
theorem chunks_word (x : Input) :
    (x.2.flatMap fun e => chunk ⟨x.1,e⟩)++[false]=outputEncoding.encode (value x) := by
  rcases x with ⟨c,es⟩
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases hp : EndpointPredicate.value ⟨c,e⟩ <;>
      simp only [List.flatMap_cons,chunk,hp,Bool.false_eq_true,↓reduceIte,
        List.nil_append,value,List.filter_cons,List.map_cons,List.append_assoc,framedListEncoding,framedListEncode] at ih ⊢
    · exact ih
    · exact congrArg (fun tail => true::(Holant.Algebraic.frame (List.replicate e.val true)++tail)) ih
noncomputable def computes : Computes inputEncoding outputEncoding value :=
  recode ((pairComputes chunksComputes (constantComputes inputEncoding Frame.wordEncoding [false])).andThen WordJoin.computes)
    id (fun _ => rfl) chunks_word
abbrev chunkMachine : Machine := (pairMachine EndpointPredicate.machine secondMachine).compose SelectedEntry.machine
abbrev chunksMachine : Machine := ContextFlatMap.machine chunkMachine
abbrev machine : Machine := (pairMachine chunksMachine (Constant.machine [false])).compose WordJoin.machine
@[simp] theorem computes_machine : computes.machine=machine := rfl
theorem inFP : InFP inputEncoding outputEncoding value := computes.inFP

def original (g : Graph) (root : g.Vertex) : Input :=
  ⟨EndpointPredicate.originalContext g root,List.finRange (ReachRound.graphEdges g).length⟩
theorem original_value (g : Graph) (root : g.Vertex) :
    value (original g root)=(surplusEdges g root).map Fin.val := by
  unfold value original surplusEdges
  have hlen : (ReachRound.graphEdges g).length=g.edges.length := by simp [ReachRound.graphEdges]
  have hmap : List.finRange (ReachRound.graphEdges g).length=
      (List.finRange g.edges.length).map (fun e => Fin.cast hlen.symm e) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj; apply Fin.ext; simp
  rw [hmap,List.filter_map,List.map_map]
  congr 1
  congr 1
  funext e
  change EndpointPredicate.value (EndpointPredicate.originalInput g root e)=_
  exact EndpointPredicate.original_value g root e
end Holant.Complexity.GraphPreprocessing.ComponentSelection.SurplusList
