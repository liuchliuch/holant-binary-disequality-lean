import Holant.Proofs.Algorithms.TransformRecognition.FiniteSystemDisjunction
import Holant.Proofs.AlgebraicRecognition.PositiveCertificateMachine.RightFold


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalDisjunctionMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open ComplexIsolation.RootSearchDriver (cross)

abbrev System := List RationalSparseMachine.Poly
abbrev systemsEncoding := framedListEncoding RationalSparseMachine.familyEncoding
abbrev Input := ℕ × List System
abbrev encoding := pairEncoding encodingNatBool systemsEncoding

def appendBranch (S T : System) : System := (cross S T).map (fun p => RationalSparseMachine.mul p.1 p.2)
def combine (width : ℕ) : List System → System
  | [] => [RationalSparseMachine.one width]
  | S::rest => appendBranch S (combine width rest)

theorem combine_fold (width : ℕ) (ss : List System) :
    combine width ss=ss.foldr appendBranch [RationalSparseMachine.one width] := by
  induction ss with
  | nil => rfl
  | cons S ss ih => simp only [combine,List.foldr_cons,ih]

theorem append_wire {v : ℕ} (S T : List (Sparse.Poly v 1)) :
    appendBranch (RationalInputMachine.bodyWire S) (RationalInputMachine.bodyWire T) =
      RationalInputMachine.bodyWire (FiniteSystemDisjunction.appendBranch S T) := by
  simp only [appendBranch,ComplexIsolation.RootSearchDriver.cross,RationalInputMachine.bodyWire,
    List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def,
    RationalSparseMachine.mul_wire,FiniteSystemDisjunction.appendBranch]

theorem combine_wire {v : ℕ} (ss : List (List (Sparse.Poly v 1))) :
    combine v (ss.map RationalInputMachine.bodyWire) =
      RationalInputMachine.bodyWire (FiniteSystemDisjunction.combine ss) := by
  induction ss with
  | nil => simp only [combine,FiniteSystemDisjunction.combine,List.map_nil,
      RationalInputMachine.bodyWire,List.map_cons,RationalSparseMachine.one_wire]
  | cons S ss ih =>
    simp only [List.map_cons,combine,ih,append_wire,FiniteSystemDisjunction.combine]

noncomputable section

def appendExecutes : Executes
    (pairEncoding RationalSparseMachine.familyEncoding RationalSparseMachine.familyEncoding)
    RationalSparseMachine.familyEncoding (fun p => appendBranch p.1 p.2) := by
  let pairs := Executes.ofComputes
    (ComplexIsolation.RootSearchDriver.crossComputes RationalSparseMachine.encoding RationalSparseMachine.encoding)
  let cell := (Executes.ofComputes
    (Wiring.secondComputes
      (pairEncoding RationalSparseMachine.familyEncoding RationalSparseMachine.familyEncoding)
      (pairEncoding RationalSparseMachine.encoding RationalSparseMachine.encoding))).comp
        RationalSparseMachine.mulExecutes
  exact NegativeCertificateMachine.Lists.map _
    (pairEncoding RationalSparseMachine.encoding RationalSparseMachine.encoding)
    RationalSparseMachine.encoding pairs (fun _ p => RationalSparseMachine.mul p.1 p.2) cell

def executes : Executes encoding RationalSparseMachine.familyEncoding (fun r : Input => combine r.1 r.2) := by
  let width := Wiring.firstComputes encodingNatBool systemsEncoding
  let ss := Wiring.secondComputes encodingNatBool systemsEncoding
  let one := (Executes.ofComputes width).comp RationalSparseMachine.oneExecutes
  let singleton := Executes.ofComputes
    ((pairComputes (identityComputes RationalSparseMachine.encoding)
      (constantComputes RationalSparseMachine.encoding RationalSparseMachine.familyEncoding [])).andThen
        (StructuralListMachine.consComputes RationalSparseMachine.encoding))
  let initial := one.comp singleton
  let prepare := (Executes.ofComputes width).pair ((Executes.ofComputes ss).pair initial)
  let body := (Executes.ofComputes (Wiring.secondComputes encodingNatBool
    (pairEncoding RationalSparseMachine.familyEncoding RationalSparseMachine.familyEncoding))).comp appendExecutes
  exact (prepare.comp (PositiveCertificateMachine.RightFold.executes encodingNatBool
    RationalSparseMachine.familyEncoding RationalSparseMachine.familyEncoding
    (fun _ => appendBranch) [] body)).congr (fun r => (combine_fold r.1 r.2).symm)

def outputs (r : Input) : TM2OutputsInTime executes.machine.computer
    (encoding.encode r) (some (RationalSparseMachine.familyEncoding.encode (combine r.1 r.2)))
    (executes.cost r) := executes.outputs r
end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalDisjunctionMachine
