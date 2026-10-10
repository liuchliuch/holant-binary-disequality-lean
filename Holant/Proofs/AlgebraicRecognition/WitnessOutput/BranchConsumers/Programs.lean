import Holant.Proofs.AlgebraicRecognition.WitnessOutput.BranchConsumers.Recovery
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionContextInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface
import Holant.Proofs.Algorithms.TransformRecognition.RawProductRecognitionMachine
import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineRecognitionMachine


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.BranchConsumers
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing GraphPreprocessing.OriginalCoefficient
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes coordinatesEncoding)
open Holant.OneHot.StackProgram.GraphLabelEncoding
noncomputable section

def variablesComputes : Computes outputEncoding PositiveCertificateMachine.vectorsEncoding
    (fun o => o.variables) := by
  let vv := pairEncoding PositiveCertificateMachine.vectorsEncoding PositiveCertificateMachine.vectorsEncoding
  let ivv := pairEncoding quadEncoding vv
  let mivv := pairEncoding quadEncoding ivv
  let rest := pairEncoding coordinatesEncoding mivv
  let roots := Wiring.secondComputes ComplexIsolation.CertificateMachine.rootEncoding rest
  let relation := Wiring.secondComputes coordinatesEncoding mivv
  let matrix := Wiring.secondComputes quadEncoding ivv
  let inverse := Wiring.secondComputes quadEncoding vv
  let scalars := Wiring.secondComputes PositiveCertificateMachine.vectorsEncoding PositiveCertificateMachine.vectorsEncoding
  exact recode (roots.andThen (relation.andThen (matrix.andThen (inverse.andThen scalars))))
    Output.wire (fun _ => rfl) (fun _ => rfl)

def selectExecutes : Executes (pairEncoding outputEncoding indicesEncoding)
    PositiveCertificateMachine.vectorsEncoding (fun p => select p.1 p.2) := by
  let cell := (Executes.ofComputes (pairComputes
    ((Wiring.firstComputes outputEncoding encodingNatBool).andThen variablesComputes)
    (Wiring.secondComputes outputEncoding encodingNatBool))).comp
      (NegativeCertificateMachine.Lists.lookup coordinatesEncoding [])
  exact Executes.mapList outputEncoding encodingNatBool coordinatesEncoding
    (fun o i => o.variables.getD i []) cell

def groupsExecutes : Executes (pairEncoding outputEncoding planEncoding) groupsEncoding
    (fun p => p.2.map (select p.1)) :=
  Executes.mapList outputEncoding indicesEncoding PositiveCertificateMachine.vectorsEncoding
    select selectExecutes

def projectExecutes : Executes (pairEncoding outputEncoding planEncoding) packetEncoding project :=
  (Executes.ofComputes (Wiring.firstComputes outputEncoding planEncoding)).pair
    ((Executes.ofComputes (Wiring.secondComputes outputEncoding planEncoding)).pair groupsExecutes)

/-- Operational Option.map for an arbitrary terminating entry program. All
tag parsing and both transfers are charged in the actual run. -/
def optionExecutes {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (w : Executes ea eb f) :
    Executes (optionEncoding ea) (optionEncoding eb) (Option.map f) where
  machine := OptionMap.machine w.machine
  cost q := match q with
    | none => 2
    | some a => 2*(ea.encode a).length+w.cost a+2*(eb.encode (f a)).length+6
  outputs q := by
    cases q with
    | none =>
      exact { steps := 2
              evals_in_steps := OptionMap.none_exact w.machine
              steps_le_m := le_rfl }
    | some a =>
      refine {
        steps := 2*(ea.encode a).length+(w.outputs a).steps+2*(eb.encode (f a)).length+6
        evals_in_steps := OptionMap.some_exact w.machine _ _ (w.outputs a).steps
          (w.outputs a).evals_in_steps
        steps_le_m := ?_ }
      have h := (w.outputs a).steps_le_m
      dsimp only
      omega

def consumeExecutes : Executes (pairEncoding resultEncoding planEncoding)
    packetResultEncoding consume := by
  let attach := (Wiring.swapComputes resultEncoding planEncoding).andThen
    (OptionContext.computes planEncoding outputEncoding)
  let swap := Executes.ofComputes (Wiring.swapComputes planEncoding outputEncoding)
  exact ((Executes.ofComputes attach).comp
    (optionExecutes (swap.comp projectExecutes))).congr
      (fun p => by rcases p with ⟨q,plan⟩; cases q <;> rfl)

def blockExecutes : Executes (pairEncoding encodingNatBool encodingNatBool)
    indicesEncoding (fun p => block p.1 p.2) := by
  let start := Wiring.firstComputes encodingNatBool encodingNatBool
  let count := Executes.ofComputes (Wiring.secondComputes encodingNatBool encodingNatBool)
  let cell := ((Wiring.firstComputes (pairEncoding encodingNatBool encodingNatBool) encodingNatBool).andThen start)
  let index := Wiring.secondComputes (pairEncoding encodingNatBool encodingNatBool) encodingNatBool
  exact NegativeCertificateMachine.Lists.map _ encodingNatBool encodingNatBool
    (count.comp RationalInputMachine.Programs.range) (fun p i => p.1+i)
    (Executes.ofComputes ((pairComputes cell index).andThen RationalInputMachine.Programs.add))

abbrev countsEncoding := pairEncoding encodingNatBool encodingNatBool
def parameterPlanExecutes : Executes countsEncoding planEncoding
    (fun p => parameterPlan p.1 p.2) := by
  let m := Executes.ofComputes (Wiring.firstComputes encodingNatBool encodingNatBool)
  let q := Executes.ofComputes (Wiring.secondComputes encodingNatBool encodingNatBool)
  let five := Executes.ofComputes (constantComputes countsEncoding encodingNatBool 5)
  let start := (five.pair q).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let specials := (start.pair m).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let p := (five.pair q).comp blockExecutes
  let empty := Executes.ofComputes (constantComputes countsEncoding indicesEncoding [])
  let originals := (start.pair m).comp blockExecutes
  let phase := (specials.pair (Executes.ofComputes
    (constantComputes countsEncoding encodingNatBool 3))).comp blockExecutes
  let cons := Executes.ofComputes (StructuralListMachine.consComputes indicesEncoding)
  let last := (phase.pair (Executes.ofComputes (constantComputes countsEncoding planEncoding []))).comp cons
  let tail := (empty.pair ((originals.pair last).comp cons)).comp cons
  exact (p.pair tail).comp cons

def localPlanExecutes : Executes encodingNatBool planEncoding localPlan := by
  let m := Executes.ofComputes (identityComputes encodingNatBool)
  let five := Executes.ofComputes (constantComputes encodingNatBool encodingNatBool 5)
  let q := (m.pair m).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let inverseStart := (five.pair m).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let originalStart := (five.pair q).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let phaseStart := (originalStart.pair m).comp (Executes.ofComputes RationalInputMachine.Programs.add)
  let p := (five.pair m).comp blockExecutes
  let inverses := (inverseStart.pair m).comp blockExecutes
  let originals := (originalStart.pair m).comp blockExecutes
  let phase := (phaseStart.pair (Executes.ofComputes
    (constantComputes encodingNatBool encodingNatBool 3))).comp blockExecutes
  let cons := Executes.ofComputes (StructuralListMachine.consComputes indicesEncoding)
  let last := (phase.pair (Executes.ofComputes (constantComputes encodingNatBool planEncoding []))).comp cons
  let tail := (inverses.pair ((originals.pair last).comp cons)).comp cons
  exact (p.pair tail).comp cons

abbrev rawEncoding := OriginalFamilyPackingMachine.encoding
def entryCount : Executes rawEncoding encodingNatBool
    (fun r => LocalAffineAllocationMachine.entries r.1) :=
  (Executes.ofComputes OriginalFamilyPackingMachine.family).comp LocalAffineAllocationMachine.entriesExecutes
def productPlanExecutes : Executes rawEncoding planEncoding
    (fun r => parameterPlan (LocalAffineAllocationMachine.entries r.1) (ProductAllocationMachine.count r.1)) :=
  (entryCount.pair RawProductRecognitionMachine.parameterCount).comp parameterPlanExecutes
def localRawPlanExecutes : Executes rawEncoding planEncoding
    (fun r => localPlan (LocalAffineAllocationMachine.entries r.1)) := entryCount.comp localPlanExecutes
def affinePlanExecutes : Executes rawEncoding planEncoding
    (fun r => parameterPlan (LocalAffineAllocationMachine.entries r.1) (r.1.length+1)) := by
  let slots := ((OriginalFamilyPackingMachine.family.andThen
    (WireLists.lengthComputes OriginalFamilyPackingMachine.vertexEncoding)).andThen UnaryBinary.computes).andThen
      RationalInputMachine.Programs.successor
  exact (entryCount.pair (Executes.ofComputes slots)).comp parameterPlanExecutes

def finish {plan : OriginalFamilyPackingMachine.Input → Plan}
    (w : Executes rawEncoding planEncoding plan) :
    Executes (pairEncoding resultEncoding rawEncoding) packetResultEncoding
      (fun p => consume (p.1,plan p.2)) :=
  (w.rightMap resultEncoding).comp consumeExecutes

/-- This program retains the actual raw input alongside the actual returned
word. It runs the original search only once and does not search for a new point. -/
def attachMachine (m : Machine) {plan : OriginalFamilyPackingMachine.Input → Plan}
    (w : Executes rawEncoding planEncoding plan) : Machine :=
  ((Wiring.diagonalComputes rawEncoding).machine.compose (LeftMap.machine m)).compose (finish w).machine

theorem attach_outputs (m : Machine) {plan : OriginalFamilyPackingMachine.Input → Plan}
    (w : Executes rawEncoding planEncoding plan) (r : OriginalFamilyPackingMachine.Input)
    (o : Option Output) (ticks : ℕ)
    (run : TM2OutputsInTime m.computer (rawEncoding.encode r)
      (some (resultEncoding.encode o)) ticks) :
    ∃ bound, Nonempty (TM2OutputsInTime (attachMachine m w).computer (rawEncoding.encode r)
      (some (packetResultEncoding.encode (consume (o,plan r)))) bound) := by
  let kept : TM2OutputsInTime (LeftMap.machine m).computer
      ((pairEncoding rawEncoding rawEncoding).encode (r,r))
      (some ((pairEncoding resultEncoding rawEncoding).encode (o,r)))
      (2*(rawEncoding.encode r).length+ticks+2*(resultEncoding.encode o).length+6) := {
    steps := 2*(rawEncoding.encode r).length+run.steps+2*(resultEncoding.encode o).length+6
    evals_in_steps := LeftMap.exact_run m _ _ _ _ run.evals_in_steps
    steps_le_m := by have h := run.steps_le_m; omega }
  let initial := (Wiring.diagonalComputes rawEncoding).outputs r
  let first := Machine.compose_correct _ _ _ _ _ _ _ initial kept
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ first ((finish w).outputs (o,r))⟩⟩

end
end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.BranchConsumers
