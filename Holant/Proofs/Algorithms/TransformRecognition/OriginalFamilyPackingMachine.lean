import Holant.Proofs.Algorithms.TransformRecognition.RationalTableMachine
import Holant.Proofs.Algorithms.TransformRecognition.StandardRootCodes


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalFamilyPackingMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Vertex := ℕ × List RootCode
abbrev Input := List Vertex × Bool
abbrev vertexEncoding := pairEncoding encodingNatBool CommonFieldMachine.rootsEncoding
abbrev familyEncoding := framedListEncoding vertexEncoding
abbrev encoding := pairEncoding familyEncoding encodingBoolBool
abbrev Output := ℕ × (List RootCode × List ℕ)
abbrev outputEncoding := pairEncoding encodingNatBool
  (pairEncoding CommonFieldMachine.rootsEncoding RationalInputMachine.addressesEncoding)

def edgeRoots (disequality : Bool) : List RootCode :=
  if disequality then [RationalRootCode.code 0,RationalRootCode.code 1,
    RationalRootCode.code 1,RationalRootCode.code 0]
  else [RationalRootCode.code 1,RationalRootCode.code 0,
    RationalRootCode.code 0,RationalRootCode.code 1]
def original (r : Input) : List RootCode := r.1.flatMap Prod.snd ++ edgeRoots r.2
def roots (r : Input) : List RootCode := original r ++
  [StandardRootCodes.imaginary,StandardRootCodes.positiveSqrtTwo]
def parameterCount (r : Input) : ℕ := r.1.length+1
def base (r : Input) : ℕ := 5+parameterCount r
def width (r : Input) : ℕ := base r + (original r).length + 3
def addresses (r : Input) : List ℕ :=
  (List.range ((original r).length+2)).map (fun j => base r+j)
def output (r : Input) : Output := (width r,roots r,addresses r)

theorem edgeRoots_length (b : Bool) : (edgeRoots b).length=4 := by cases b <;> rfl
theorem roots_length (r : Input) : (roots r).length=(original r).length+2 := by simp [roots]
theorem addresses_length (r : Input) : (addresses r).length=(roots r).length := by
  simp only [addresses,List.length_map,List.length_range,roots_length]
theorem address_at (r : Input) (j : Fin (roots r).length) :
    (addresses r).getD j.val 0=base r+j.val := by
  have hj : j.val < (original r).length+2 := by simpa only [roots_length] using j.isLt
  simp [addresses,List.getD_eq_getElem?_getD,hj]
theorem address_lt_width (r : Input) (j : Fin (roots r).length) :
    (addresses r).getD j.val 0 < width r := by
  rw [address_at]
  have hj : j.val < (original r).length+2 := by simpa only [roots_length] using j.isLt
  unfold width
  omega
theorem original_prefix (r : Input) : (roots r).take (original r).length=original r := by
  simp [roots]

noncomputable section
def family := Wiring.firstComputes familyEncoding encodingBoolBool
def edgeFlag := Wiring.secondComputes familyEncoding encodingBoolBool
def vertexRoots : Computes familyEncoding CommonFieldMachine.rootsEncoding
    (fun xs : List Vertex => xs.flatMap Prod.snd) :=
  congrComputes ((WireLists.mapComputes vertexEncoding CommonFieldMachine.rootsEncoding Prod.snd
    (Wiring.secondComputes encodingNatBool CommonFieldMachine.rootsEncoding)).andThen
      (WireLists.flatten ComplexIsolation.CertificateMachine.rootEncoding))
    (fun _ => by simp only [List.flatMap_def,Function.comp_apply])
def edgeComputes : Computes encodingBoolBool CommonFieldMachine.rootsEncoding edgeRoots :=
  GraphPreprocessing.FiniteRecode.computes _ _ edgeRoots 1 (fun b => by cases b <;> rfl)
def originalComputes : Computes encoding CommonFieldMachine.rootsEncoding original :=
  (pairComputes (family.andThen vertexRoots) (edgeFlag.andThen edgeComputes)).andThen
    (WireLists.append ComplexIsolation.CertificateMachine.rootEncoding)
def rootsComputes : Computes encoding CommonFieldMachine.rootsEncoding roots :=
  (pairComputes originalComputes (constantComputes encoding CommonFieldMachine.rootsEncoding
    [StandardRootCodes.imaginary,StandardRootCodes.positiveSqrtTwo])).andThen
      (WireLists.append ComplexIsolation.CertificateMachine.rootEncoding)
def parameters : Computes encoding encodingNatBool parameterCount :=
  (((family.andThen (WireLists.lengthComputes vertexEncoding)).andThen GraphPreprocessing.UnaryBinary.computes).andThen
    RationalInputMachine.Programs.successor)
def baseComputes : Computes encoding encodingNatBool base :=
  (pairComputes (constantComputes encoding encodingNatBool 5) parameters).andThen RationalInputMachine.Programs.add
def originalsCount := (originalComputes.andThen (WireLists.lengthComputes ComplexIsolation.CertificateMachine.rootEncoding)).andThen
  GraphPreprocessing.UnaryBinary.computes
def rootCount : Computes encoding encodingNatBool (fun r => (original r).length+2) :=
  (pairComputes originalsCount (constantComputes encoding encodingNatBool 2)).andThen RationalInputMachine.Programs.add
def widthComputes : Computes encoding encodingNatBool width :=
  (pairComputes ((pairComputes baseComputes originalsCount).andThen RationalInputMachine.Programs.add)
    (constantComputes encoding encodingNatBool 3)).andThen RationalInputMachine.Programs.add

def addressCell : Executes (pairEncoding encoding encodingNatBool) encodingNatBool
    (fun p : Input × ℕ => base p.1+p.2) :=
  Executes.ofComputes ((pairComputes
    ((Wiring.firstComputes encoding encodingNatBool).andThen baseComputes)
    (Wiring.secondComputes encoding encodingNatBool)).andThen RationalInputMachine.Programs.add)
def addressesExecutes : Executes encoding RationalInputMachine.addressesEncoding addresses :=
  NegativeCertificateMachine.Lists.map encoding encodingNatBool encodingNatBool
    ((Executes.ofComputes rootCount).comp RationalInputMachine.Programs.range)
    (fun r j => base r+j) addressCell
def executes : Executes encoding outputEncoding output :=
  (Executes.ofComputes widthComputes).pair ((Executes.ofComputes rootsComputes).pair addressesExecutes)

def outputs (r : Input) : TM2OutputsInTime executes.machine.computer
    (encoding.encode r) (some (outputEncoding.encode (output r))) (executes.cost r) := executes.outputs r
theorem primitive_bound (r : Input) :
    primitiveCost executes.machine (executes.outputs r).steps
      (some (initList executes.machine.computer (encoding.encode r))) ≤
        executes.cost r * executes.machine.primitiveBudget := executes.primitive_bound r
end
end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalFamilyPackingMachine
