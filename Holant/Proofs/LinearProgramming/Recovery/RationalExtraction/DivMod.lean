import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Euclidean
import Holant.Proofs.LinearProgramming.Foundation.RoundingProgram
import Holant.Proofs.LinearProgramming.Foundation.Infrastructure.Arithmetic
import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Codec
import Holant.Complexity.StackProtocol

set_option autoImplicit false

/-! Kernel-checked recovery component. The quotient AND remainder are produced by the existing
finite bit long-division programs. Two physical runs are charged; Nat.div and
Nat.mod below are their proved specification, never machine opcodes.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction.DivMod
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines StackProtocol
noncomputable section

abbrev selectedMachine (out : Bool) : Machine where
  K := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).K
  decidableK := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).kDecidableEq
  finiteK := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).kFin
  input := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).k₀
  output := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).k₁
  Label := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).Λ
  finiteLabel := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).ΛFin
  main := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).main
  State := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).σ
  finiteState := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).σFin
  initial := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).initialState
  program := (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.computer out).m

def reversedRemainder : Computes
    (pairEncoding (reverseEncoding encodingNatBool) (reverseEncoding encodingNatBool))
    encodingNatBool (fun p => p.1 % p.2) where
  machine := selectedMachine true
  time := Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.remainderPolyTime.time
  outputs p := by
    have h := Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.remainderPolyTime.outputsFun p
    change TM2OutputsInTime (selectedMachine true).computer
      (List.map id (Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1 % p.2)))) _ at h
    simpa only [List.map_id,pairEncoding,reverseEncoding,
      Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.EncodedDivision.inputEncoding,
      BinaryArithmetic.EncodedAddition.inputEncoding,encodingNatBool] using h

def quotient := RoundingProgram.divide
def remainder : Computes (pairEncoding encodingNatBool encodingNatBool) encodingNatBool
    (fun p => p.1 % p.2) :=
  (RationalArithmetic.reversePairComputes encodingNatBool encodingNatBool).andThen reversedRemainder
def computes : Computes (pairEncoding encodingNatBool encodingNatBool)
    (pairEncoding encodingNatBool encodingNatBool) (fun p => (p.1/p.2,p.1%p.2)) :=
  pairComputes quotient remainder

theorem execution (p : ℕ × ℕ) :
    Holant.Complexity.StackProtocol.RunsExactly computes.machine.computer.step
      (initList computes.machine.computer ((pairEncoding encodingNatBool encodingNatBool).encode p))
      (haltList computes.machine.computer
        ((pairEncoding encodingNatBool encodingNatBool).encode (p.1/p.2,p.1%p.2)))
      (computes.outputs p).steps := (computes.outputs p).evals_in_steps
theorem time_bound (p : ℕ × ℕ) : (computes.outputs p).steps≤
    computes.time.eval ((pairEncoding encodingNatBool encodingNatBool).encode p).length :=
  (computes.outputs p).steps_le_m
theorem word_bound (p : ℕ × ℕ) :
    ((pairEncoding encodingNatBool encodingNatBool).encode (p.1/p.2,p.1%p.2)).length≤
      computes.outputBound.bound.eval ((pairEncoding encodingNatBool encodingNatBool).encode p).length :=
  computes.outputBound.length_le p
theorem primitive_bound (p : ℕ × ℕ) :
    primitiveCost computes.machine (computes.outputs p).steps
      (some (initList computes.machine.computer ((pairEncoding encodingNatBool encodingNatBool).encode p)))≤
        (primitivePolynomial computes).eval ((pairEncoding encodingNatBool encodingNatBool).encode p).length :=
  computes_primitive_cost computes p

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction.DivMod
