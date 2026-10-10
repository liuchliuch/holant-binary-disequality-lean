import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.Indexed
import Holant.Proofs.Counting.RawGraphMachine.Algorithm
import Holant.Proofs.Counting.VerifierCompiler.Stateful.CapacityFrontend.ListAccess


noncomputable section
namespace Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access
open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler UniversalPairReduction.SmoothingCompiler
open VerifierCompiler.Stateful
open VerifierCompiler.Stateful.CapacityFrontend

variable {A B : Type}
abbrev unary := Unary.encoding
def boundedEncoding := pairEncoding unary encodingNatBool

theorem prefix_word (n j : ℕ) :
    (List.range n).flatMap (fun i => if i < j then [true] else []) =
      List.replicate (min n j) true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    by_cases h : n < j
    · simp [h, Nat.min_eq_left (Nat.le_of_lt h), Nat.min_eq_left (by omega : n + 1 ≤ j),
        List.replicate_add]
    · simp [h, Nat.min_eq_right (by omega : j ≤ n),
        Nat.min_eq_right (by omega : j ≤ n + 1)]

def boundedUnary : Computes boundedEncoding unary (fun p => min p.1 p.2) := by
  let query := pairEncoding boundedEncoding unary
  let context := Wiring.firstComputes boundedEncoding unary
  let target := context.andThen (Wiring.secondComputes unary encodingNatBool)
  let index := (Wiring.secondComputes boundedEncoding unary).andThen UnaryBinary.computes
  let test := (pairComputes index target).andThen Endpoints.lessComputes
  let cell := ifComputes test (constantComputes query Frame.wordEncoding [true])
    (constantComputes query Frame.wordEncoding [])
  refine recode (BinaryInterpolation.WeightCompiler.rangeWordsComputes boundedEncoding Prod.fst
    (Wiring.firstComputes unary encodingNatBool) _ cell) id (fun _ => rfl) ?_
  intro p
  simpa [Frame.wordEncoding, unary, Unary.encoding, Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.RuntimeParameters.unary,
    UnaryBinary.unaryEncoding] using prefix_word p.1 p.2

theorem getD_min (xs : List A) (j : ℕ) (d : A) :
    xs.getD (min xs.length j) d = xs.getD j d := by
  by_cases h : j < xs.length
  · rw [Nat.min_eq_right (Nat.le_of_lt h)]
  · have hj : xs.length ≤ j := by omega
    rw [Nat.min_eq_left hj]
    rw [List.getD_eq_default _ _ le_rfl, List.getD_eq_default _ _ hj]

def lookupEncoding (e : Encoding A Bool) := pairEncoding (framedListEncoding e) encodingNatBool
def lookup (e : Encoding A Bool) (d : A) :
    Computes (lookupEncoding e) e (fun p => p.1.getD p.2 d) := by
  let xs := Wiring.firstComputes (framedListEncoding e) encodingNatBool
  let j := Wiring.secondComputes (framedListEncoding e) encodingNatBool
  let cap := (pairComputes (xs.andThen (Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed.countComputes e)) j).andThen boundedUnary
  exact congrComputes ((pairComputes xs cap).andThen (ListAccess.getDComputes e d))
    (fun p => getD_min p.1 p.2 d)

def updateEncoding (e : Encoding A Bool) :=
  pairEncoding (framedListEncoding e) (pairEncoding encodingNatBool e)

def update (e : Encoding A Bool) (d : A) :
    Computes (updateEncoding e) (framedListEncoding e) (fun p => p.1.set p.2.1 p.2.2) := by
  let base := updateEncoding e
  let xs := Wiring.firstComputes (framedListEncoding e) (pairEncoding encodingNatBool e)
  let query := pairEncoding base unary
  let context := Wiring.firstComputes base unary
  let arr := context.andThen xs
  let tail := context.andThen (Wiring.secondComputes (framedListEncoding e) (pairEncoding encodingNatBool e))
  let j := tail.andThen (Wiring.firstComputes encodingNatBool e)
  let value := tail.andThen (Wiring.secondComputes encodingNatBool e)
  let i := Wiring.secondComputes base unary
  let same := (pairComputes (i.andThen UnaryBinary.computes) j).andThen Endpoints.equalComputes
  let old := (pairComputes arr i).andThen (ListAccess.getDComputes e d)
  let cell := ifComputes same value old
  refine congrComputes (ListAccess.rangeComputes base e (fun p => p.1.length)
    (xs.andThen (Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed.countComputes e)) _ cell) ?_
  intro p
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h : i < p.1.length := by simpa using hi
    simp [List.getElem_set, List.getD_eq_getElem, h, eq_comm]

def tail (e : Encoding A Bool) (d : A) :
    Computes (framedListEncoding e) (framedListEncoding e) List.tail := by
  let base := framedListEncoding e
  let xs := Wiring.firstComputes base unary
  let i := (Wiring.secondComputes base unary).andThen Unary.successorComputes
  let cell := (pairComputes xs i).andThen (ListAccess.getDComputes e d)
  refine congrComputes (ListAccess.rangeComputes base e (fun xs => xs.length - 1)
    ((Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Indexed.countComputes e).andThen Endpoints.unaryPredecessorComputes) _ cell) ?_
  intro xs
  cases xs with
  | nil => simp
  | cons x xs =>
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have h : i < xs.length := by simpa using hj
      simp [List.getD_eq_getElem, h]

/-- Two-entry framing is reused to make a physical cons, with variable element
width and no implicit memory allocation. -/
def cons (e : Encoding A Bool) :
    Computes (pairEncoding e (framedListEncoding e)) (framedListEncoding e)
      (fun p => p.1 :: p.2) :=
  recode (joinComputes
    ((Wiring.firstComputes e (framedListEncoding e)).andThen (entryComputes e))
    ((Wiring.secondComputes e (framedListEncoding e)).andThen (encodeComputes (framedListEncoding e))))
    id (fun _ => rfl) (fun _ => rfl)

def list₁ {ea : Encoding A Bool} (eb : Encoding B Bool) {f : A → B}
    (w : Computes ea eb f) : Computes ea (framedListEncoding eb) (fun a => [f a]) :=
  (pairComputes w (constantComputes ea (framedListEncoding eb) [])).andThen (cons eb)

def list₃ {ea : Encoding A Bool} (eb : Encoding B Bool) {f g h : A → B}
    (u : Computes ea eb f) (v : Computes ea eb g) (w : Computes ea eb h) :
    Computes ea (framedListEncoding eb) (fun a => [f a, g a, h a]) :=
  (pairComputes u ((pairComputes v (list₁ eb w)).andThen (cons eb))).andThen (cons eb)

end Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access
