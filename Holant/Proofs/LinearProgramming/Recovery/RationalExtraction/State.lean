import Holant.Proofs.LinearProgramming.Foundation.ExactSolve.LengthCounter
import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.RationalExtraction.Initialize

set_option autoImplicit false

/-! Kernel-checked recovery component. Actual endpoint bytes remain in every state. Once a
certified result is obtained it is retained. The only loop fuel is 2L+4, with
L obtained by the physical byte counter; no binary D is converted to unary.
Termination separately connects this produced fuel to the actual status bytes.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open FixedGadgetSubstitution.Compiler
noncomputable section

abbrev Payload := Query × Result
def payloadEncoding := pairEncoding queryEncoding resultEncoding
abbrev State := ℕ × Payload
def stateEncoding := pairEncoding encodingNatBool payloadEncoding
def bodyEncoding := pairEncoding encodingBoolBool stateEncoding
def advance (p : Payload) : Payload :=
  if done p.2 then p else (p.1,Jump.step (p.1,neighbors p.2))
def «at» (q : Query) : ℕ → Payload
  | 0 => (q,Initialize.value q)
  | k+1 => advance («at» q k)
def rounds (q : Query) : ℕ := 2*(queryEncoding.encode q).length+4
def initial (q : Query) : State := (rounds q,«at» q 0)
def finish : ℕ → Payload → State
  | 0,p => (0,p)
  | k+1,p => finish k (advance p)
def resultState (q : Query) : State := finish (rounds q) («at» q 0)
def value (q : Query) : Result := (resultState q).2.2

def source : Computes payloadEncoding queryEncoding (fun p : Payload => p.1) := Wiring.firstComputes _ _
def receipt : Computes payloadEncoding resultEncoding (fun p : Payload => p.2) := Wiring.secondComputes _ _
def doneComputes : Computes resultEncoding encodingBoolBool done :=
  (Wiring.firstComputes _ _).andThen (Wiring.firstComputes _ _)
def neighborsComputes : Computes resultEncoding neighborsEncoding neighbors :=
  (Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _)
def advanceComputes : Computes payloadEncoding payloadEncoding advance :=
  congrComputes (ifComputes (receipt.andThen doneComputes)
    (identityComputes payloadEncoding)
    (pairComputes source
      ((pairComputes source (receipt.andThen neighborsComputes)).andThen Programs.computes)))
    (fun p => by simp [advance])
def countLength : Computes queryEncoding UnaryBinary.unaryEncoding
    (fun q : Query => (queryEncoding.encode q).length) :=
  (encodeComputes queryEncoding).andThen Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.LengthCounter.computes
def countUnary : Computes queryEncoding UnaryBinary.unaryEncoding rounds :=
  congrComputes ((((((pairComputes countLength countLength).andThen AccessPrograms.unaryAdd).andThen
    WireLists.succComputes).andThen WireLists.succComputes).andThen WireLists.succComputes).andThen
      WireLists.succComputes) (fun q => by simp [rounds]; omega)
def countBinary : Computes queryEncoding encodingNatBool rounds := countUnary.andThen UnaryBinary.computes
def prepare : Computes queryEncoding stateEncoding initial :=
  pairComputes countBinary (pairComputes (identityComputes queryEncoding) Initialize.computes)

@[simp] theorem advance_source (p : Payload) : (advance p).1=p.1 := by
  unfold advance
  split <;> rfl

@[simp] theorem at_source (q : Query) (k : ℕ) : («at» q k).1=q := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [«at»,advance]; split <;> exact ih
theorem finish_exact (q : Query) (k r : ℕ) : finish r («at» q k)=(0,«at» q (k+r)) := by
  induction r generalizing k with
  | zero => simp [finish]
  | succ r ih =>
    change finish r («at» q (k+1))=_
    rw [ih]
    congr 2
    omega
@[simp] theorem result_exact (q : Query) : resultState q=(0,«at» q (rounds q)) := by
  simpa [resultState] using finish_exact q 0 (rounds q)
theorem advance_safe (p : Payload) (hq : Valid p.1) (hp : Jump.Safe p.1 p.2) :
    Jump.Safe (advance p).1 (advance p).2 := by
  cases h : done p.2 with
  | true => simpa [advance,h] using hp
  | false => simpa [advance,h] using Jump.step_safe p.1 (neighbors p.2) hq (hp.2.2 h)
theorem at_safe (q : Query) (hq : Valid q) (k : ℕ) : Jump.Safe q («at» q k).2 := by
  induction k with
  | zero => exact Initialize.safe q hq
  | succ k ih =>
    simpa only [«at»,advance_source,at_source] using advance_safe («at» q k) (by simpa using hq) (by simpa using ih)
theorem value_safe (q : Query) (hq : Valid q) : Jump.Safe q (value q) := by
  simpa only [value,result_exact] using at_safe q hq (rounds q)
theorem terminal_retained (p : Payload) (h : done p.2=true) : advance p=p := by simp [advance,h]
theorem done_monotone (q : Query) (k : ℕ) :
    done («at» q k).2=true → done («at» q (k+1)).2=true := by
  intro h
  simp [«at»,terminal_retained («at» q k) h,h]

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.RationalExtraction
