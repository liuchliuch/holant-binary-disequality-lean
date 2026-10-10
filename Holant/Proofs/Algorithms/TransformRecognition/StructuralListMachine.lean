import Holant.Proofs.Algorithms.TransformRecognition.StructuredCatalogue
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Iteration


namespace Holant.LocalDrafts.MainChain.TransformRecognition.StructuralListMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.EffectiveAlgebraic.ComplexIsolation
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
variable {A : Type} (e : Encoding A Bool)

abbrev listEncoding := framedListEncoding e
abbrev familyEncoding := framedListEncoding (listEncoding e)
abbrev State (A : Type) := List A × List (List A)
abbrev stateEncoding := pairEncoding (listEncoding e) (familyEncoding e)

def exactLength (xs : List A) (n : ℕ) : List (List A) :=
  (FiniteBranchEnumeration.vectors xs n).map List.ofFn
def step (s : State A) : State A :=
  (s.1,(RootSearchDriver.cross s.1 s.2).map (fun p => p.1::p.2))

theorem exactLength_zero (xs : List A) : exactLength xs 0=[[]] := rfl
theorem exactLength_succ (xs : List A) (n : ℕ) :
    exactLength xs (n+1)=(RootSearchDriver.cross xs (exactLength xs n)).map (fun p => p.1::p.2) := by
  simp [exactLength,FiniteBranchEnumeration.vectors,RootSearchDriver.cross,
    List.map_flatMap,List.map_map,List.ofFn_succ,Function.comp_def]
theorem iterate_start (xs : List A) (n : ℕ) :
    (step^[n]) (xs,[[]])=(xs,exactLength xs n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,step,exactLength_succ]

noncomputable section

def consComputes : Computes (pairEncoding e (listEncoding e)) (listEncoding e)
    (fun p => p.1::p.2) :=
  recode (joinComputes
    ((Wiring.firstComputes e (listEncoding e)).andThen (entryComputes e))
    ((Wiring.secondComputes e (listEncoding e)).andThen (encodeComputes (listEncoding e))))
      id (fun _ => rfl) (fun _ => rfl)

def stepComputes : Computes (stateEncoding e) (stateEncoding e) (step (A:=A)) :=
  pairComputes (Wiring.firstComputes (listEncoding e) (familyEncoding e))
    ((RootSearchDriver.crossComputes e (listEncoding e)).andThen
      (WireLists.mapComputes (pairEncoding e (listEncoding e)) (listEncoding e)
        (fun p => p.1::p.2) (consComputes e)))

abbrev exactInputEncoding := pairEncoding encodingNatBool (listEncoding e)
def exactExecutes : Executes (exactInputEncoding e) (familyEncoding e)
    (fun p => exactLength p.2 p.1) := by
  let n := Wiring.firstComputes encodingNatBool (listEncoding e)
  let xs := Wiring.secondComputes encodingNatBool (listEncoding e)
  let initial := pairComputes xs (constantComputes (exactInputEncoding e) (familyEncoding e) [[]])
  let prepare := Executes.ofComputes (pairComputes n initial)
  let loop := Iteration.executes (stateEncoding e) (Executes.ofComputes (stepComputes e))
  let output := Executes.ofComputes (Wiring.secondComputes (listEncoding e) (familyEncoding e))
  exact Executes.congr ((prepare.comp loop).comp output) (fun p => by rw [iterate_start])

/-- Only a conversion of already proved concrete timed runs. The actual
RootSearchDriver.Height machine, not an arbitrary iterator, is used below. -/
def ofFinite {B C : Type} {eb : Encoding B Bool} {ec : Encoding C Bool} {f : B → C}
    (w : CertificateMachine.FiniteComputes eb ec f) : Executes eb ec f :=
  ⟨w.machine,fun b => w.time (eb.encode b).length,w.outputs⟩

abbrev boundedInputEncoding := pairEncoding (listEncoding e) encodingNatBool
def counts : Executes (boundedInputEncoding e)
    (framedListEncoding UnaryBinary.unaryEncoding) (fun p => List.range (p.2+1)) :=
  ((Executes.ofComputes (Wiring.secondComputes (listEncoding e) encodingNatBool)).comp
    (ofFinite RootSearchDriver.Height.binaryToUnary)).comp
      (Executes.ofComputes (WireLists.succComputes.andThen ComponentSelection.UnaryRange.computes))

def eachLength : Executes (pairEncoding (boundedInputEncoding e) UnaryBinary.unaryEncoding)
    (familyEncoding e) (fun p => exactLength p.1.1 p.2) := by
  let xs := (Wiring.firstComputes (boundedInputEncoding e) UnaryBinary.unaryEncoding).andThen
    (Wiring.firstComputes (listEncoding e) encodingNatBool)
  let n := (Wiring.secondComputes (boundedInputEncoding e) UnaryBinary.unaryEncoding).andThen
    UnaryBinary.computes
  exact (Executes.ofComputes (pairComputes n xs)).comp (exactExecutes e)

def boundedExecutes : Executes (boundedInputEncoding e) (familyEncoding e)
    (fun p => StructuredCatalogue.lists p.1 p.2) := by
  let prepared := Executes.pair (Executes.ofComputes (identityComputes (boundedInputEncoding e)))
    (counts e)
  let families := Executes.mapList (boundedInputEncoding e) UnaryBinary.unaryEncoding
    (familyEncoding e) (fun p n => exactLength p.1 n) (eachLength e)
  let flattened := (prepared.comp families).comp (Executes.ofComputes (WireLists.flatten (listEncoding e)))
  exact Executes.congr flattened (fun p => by
    simp only [id_eq,StructuredCatalogue.lists,exactLength,List.flatMap_def])

def bounded_outputs (xs : List A) (h : ℕ) :
    TM2OutputsInTime (boundedExecutes e).machine.computer
      ((boundedInputEncoding e).encode (xs,h))
      (some ((familyEncoding e).encode (StructuredCatalogue.lists xs h)))
      ((boundedExecutes e).cost (xs,h)) := (boundedExecutes e).outputs (xs,h)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.StructuralListMachine
