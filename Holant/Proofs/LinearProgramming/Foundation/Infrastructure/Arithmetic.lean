import Holant.Complexity.BinaryCompose.OutputBound
import Holant.Complexity.BinaryArithmetic.EncodedAddition
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists
import Holant.Complexity.FixedFieldMachines.Reverse

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure
open Turing Computability Holant.Complexity BinaryCompose BinaryArithmetic FixedFieldMachines GraphPreprocessing

abbrev additionMachine : Machine where
  K := EncodedAddition.computer.K
  input := EncodedAddition.computer.k₀
  output := EncodedAddition.computer.k₁
  Label := EncodedAddition.computer.Λ
  main := EncodedAddition.computer.main
  State := EncodedAddition.computer.σ
  initial := EncodedAddition.computer.initialState
  program := EncodedAddition.computer.m

noncomputable def additionComputes :
    Computes EncodedAddition.inputEncoding encodingNatBool (fun p => p.1 + p.2) where
  machine := additionMachine
  time := EncodedAddition.additionPolyTime.time
  outputs p := by
    have h := EncodedAddition.additionPolyTime.outputsFun p
    change TM2OutputsInTime additionMachine.computer (List.map id (EncodedAddition.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1 + p.2)))) _ at h
    simpa only [List.map_id] using h

/-- Existing carry addition with actual bit reversals for both encoded operands. -/
noncomputable def addComputes : Computes (pairEncoding encodingNatBool encodingNatBool)
    encodingNatBool (fun p => p.1 + p.2) := by
  let prepare := pairComputes
    ((Wiring.firstComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
    ((Wiring.secondComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
  let ready : Computes (pairEncoding encodingNatBool encodingNatBool)
      BinaryArithmetic.EncodedAddition.inputEncoding id :=
    recode prepare id (fun _ => rfl) (fun _ => rfl)
  exact ready.andThen additionComputes

end Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure
