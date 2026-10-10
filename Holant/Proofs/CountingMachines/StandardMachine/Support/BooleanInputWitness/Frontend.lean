import Holant.Proofs.CountingMachines.StandardMachine.Support.BooleanInputWitness.Routing
import Holant.Proofs.CountingMachines.StandardMachine.Support.GeneralVerifierOutput.Source

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. An actual sequential/fanout finite-machine consumer:
original coded bytes -> original N -> original P(N), checked canonical suffix,
same old verifier payload and strict old-result decoder. All polynomial times
and transfer costs are inherited from the returned literal programs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Frontend
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support
open BooleanOpcode
variable {α Γ : Type} [Fintype Γ] {ea : Encoding α Γ} {f : α → ℕ}
variable (w : SharpPWitness ea f)

def dataEncoding : Encoding (α × List Bool) Bool :=
  FixedFieldMachines.pairEncoding (inputEncoding w) Frame.wordEncoding

def inputBytes : Computes (dataEncoding w) Frame.wordEncoding
    (fun p => (inputEncoding w).encode p.1) :=
  (Wiring.firstComputes (inputEncoding w) Frame.wordEncoding).andThen
    (encodeComputes (inputEncoding w))

def oldCounter : Computes (dataEncoding w) WitnessParameters.unary
    (fun p => oldLength w p.1) :=
  (Wiring.firstComputes (inputEncoding w) Frame.wordEncoding).andThen
    (Counter.oldWitnessComputes w)

def witnessBits : Computes (dataEncoding w) Frame.wordEncoding Prod.snd :=
  Wiring.secondComputes (inputEncoding w) Frame.wordEncoding

def guardInput : Computes (dataEncoding w) Guard.rawEncoding
    (fun p => (oldLength w p.1,p.2)) :=
  recode (joinComputes
    ((oldCounter w).andThen (encodeComputes WitnessParameters.unary))
    (joinComputes (constantComputes (dataEncoding w) Frame.wordEncoding [false])
      (witnessBits w))) id (fun _ => rfl)
    (fun _ => by simp [Guard.rawEncoding,WitnessParameters.unary,
      UnaryBinary.unaryEncoding,Frame.wordEncoding])

def guarded : Computes (dataEncoding w) Guard.outputEncoding
    (fun p => Padding.extract (oldLength w p.1) p.2) :=
  (guardInput w).andThen Guard.rawComputes

def acceptedPrefix : Computes (dataEncoding w) Frame.wordEncoding
    (fun p => (Padding.extract (oldLength w p.1) p.2).getD []) :=
  (guarded w).andThen Routing.Prefix.computes

def guardFlag : Computes (dataEncoding w) encodingBoolBool
    (fun p => (Padding.extract (oldLength w p.1) p.2).isSome) :=
  (guarded w).andThen Routing.Flag.computes

/-- The two entries are the original actual input alphabet representatives
of Sum.inr false/true, with the original fixed-bit table. -/
def witnessTable (bit : Bool) : List Bool :=
  Code.symbol (original w) (original w).core.k₀
    (w.verifier.inputAlphabet.symm (Sum.inr bit))

theorem append_payload (a : α) (bits : List Bool) :
    (inputEncoding w).encode a ++ bits.flatMap (witnessTable w) =
      (pairEncoding w).encode (a,bits) := by
  simp [inputEncoding,pairEncoding,payload,witnessTable,Code.word,
    encodingProd,encodingList,List.flatMap_map,Function.comp_def]
  rfl

def codedPrefix : Computes (dataEncoding w) Frame.wordEncoding
    (fun p => ((Padding.extract (oldLength w p.1) p.2).getD []).flatMap (witnessTable w)) :=
  (acceptedPrefix w).andThen (Routing.LiteralMap.computes (witnessTable w))

def oldPayload : Computes (dataEncoding w) (pairEncoding w)
    (fun p => (p.1,(Padding.extract (oldLength w p.1) p.2).getD [])) :=
  recode (joinComputes (inputBytes w) (codedPrefix w)) id (fun _ => rfl)
    (fun p => append_payload w p.1 _)

/-- The old verifier is run on precisely the regenerated OLD pair. Its old
singleton result code is decoded by the separate strict finite reader. -/
def oldAnswer : Computes (dataEncoding w) encodingBoolBool
    (fun p => w.accept (p.1,(Padding.extract (oldLength w p.1) p.2).getD [])) :=
  (oldPayload w).andThen
    (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.GeneralVerifierOutput.Source.computes w)

def conjunction : Computes
    (FixedFieldMachines.pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p => p.1 && p.2) :=
  FiniteRecode.computes
    (FixedFieldMachines.pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p => p.1 && p.2) 4
    (fun p => by cases p.1 <;> cases p.2 <;> rfl)

/-- Every input, including a too-short candidate and a noncanonical suffix,
has a genuine clean run. Rejecting guards remain false even if the old verifier
would accept the empty prefix. No branch/verdict is provided by the caller. -/
def computes : Computes (dataEncoding w) encodingBoolBool (paddedAccept w) :=
  congrComputes ((pairComputes (guardFlag w) (oldAnswer w)).andThen conjunction)
    (fun p => by
      cases h : Padding.extract (oldLength w p.1) p.2 <;>
        simp [paddedAccept,Padding.accept,h])

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.BooleanInputWitness.Frontend
