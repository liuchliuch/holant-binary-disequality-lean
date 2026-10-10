import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BitmapRoundInterface
import Holant.Complexity.FixedFieldMachines.MachineSyntax

/-! A real synchronous next layer and original-edge parent probe on the same
immutable previous bitmap. Fixed wire machines remove the target word for the
round; the original scan retains false-end/true-end and original edge order. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentProbe
open Turing Computability BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev Input := NeighborScan.Input
abbrev inputEncoding := NeighborScan.inputEncoding
def outputEncoding := pairEncoding Frame.wordEncoding ParentRowEncoding.parent

def wordPair := pairEncoding Frame.wordEncoding Frame.wordEncoding
def wordEntry := pairEncoding Frame.wordEncoding wordPair
noncomputable def bitmapComputes : Computes wordEntry Frame.wordEncoding (fun x => x.1) :=
  Wiring.firstComputes Frame.wordEncoding wordPair
noncomputable def edgesComputes : Computes wordEntry Frame.wordEncoding (fun x => x.2.2) :=
  (Wiring.secondComputes Frame.wordEncoding wordPair).andThen
    (Wiring.secondComputes Frame.wordEncoding Frame.wordEncoding)
noncomputable def wireComputes : Computes wordEntry wordPair (fun x => (x.1,x.2.2)) :=
  pairComputes bitmapComputes edgesComputes

abbrev edgesMachine : Machine := secondMachine.compose secondMachine
abbrev wireMachine : Machine := pairMachine Wiring.firstMachine edgesMachine

def roundInput (x : Input) : BitmapRound.Input := ⟨x.1,x.2.2⟩
noncomputable def prepareComputes : Computes inputEncoding BitmapRound.inputEncoding roundInput :=
  recode wireComputes (fun x => (x.1,(List.replicate x.2.1.val true,NeighborScan.edgeBits x.2.2)))
    (fun _ => rfl) (fun _ => rfl)
noncomputable def roundComputes : Computes inputEncoding Frame.wordEncoding (fun x => BitmapRound.value (roundInput x)) :=
  prepareComputes.andThen BitmapRound.computes

def value (x : Input) : List Bool × Option (ℕ × Bool) :=
  (BitmapRound.value (roundInput x),NeighborScan.value x)
abbrev roundMachine : Machine := wireMachine.compose (BitmapRound.machine BitmapRound.neighborMachine)
abbrev machine : Machine := pairMachine roundMachine (NeighborScan.machine NeighborScan.actual)
noncomputable def computes : Computes inputEncoding outputEncoding value :=
  pairComputes roundComputes NeighborScan.computes
@[simp] theorem computes_machine : computes.machine=machine := rfl
noncomputable def timePolynomial : Polynomial ℕ := computes.time
theorem inFP : InFP inputEncoding outputEncoding value := computes.inFP

@[simp] theorem value_bitmap_length (x : Input) : (value x).1.length=x.1.length := by simp [value,roundInput]

theorem graph_value (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) :
    value (NeighborScan.graphInput g s target) =
      (NeighborPredicate.bitmap g (g.round s),(g.neighborRun s target).1.map (fun q => (q.1.val,q.2))) := by
  change (BitmapRound.value (BitmapRound.graphInput g s),NeighborScan.value (NeighborScan.graphInput g s target)) = _
  rw [BitmapRound.graph_value,NeighborScan.graph_value]

noncomputable def graph_timed (g : Graph) (s : Finset g.Vertex) (target : g.Vertex) :
    TM2OutputsInTime machine.computer
      (NeighborScan.inputWord (NeighborPredicate.bitmap g s) (List.replicate target.val true) (ReachRound.graphEdges g))
      (some (Holant.Algebraic.frame (NeighborPredicate.bitmap g (g.round s))++
        ParentRowEncoding.parent.encode ((g.neighborRun s target).1.map (fun q => (q.1.val,q.2)))))
      (timePolynomial.eval (NeighborScan.inputWord (NeighborPredicate.bitmap g s)
        (List.replicate target.val true) (ReachRound.graphEdges g)).length) := by
  simpa only [computes_machine,timePolynomial,NeighborScan.graph_input_word,graph_value,outputEncoding,pairEncoding,Frame.wordEncoding,id_eq] using
    computes.outputs (NeighborScan.graphInput g s target)

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ParentProbe
