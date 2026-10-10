import Holant.Proofs.Tractability.EOEvaluation.RawColumns
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators


namespace Holant.LocalDrafts.Tractability.EOEvaluation.MatrixCells
open Computability Holant.Tractable Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
open AffineMachine LocalAffineMachine.Relabel RawColumns
open Holant.Complexity.UniversalPairReduction.SmoothingCompiler
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}

def vertexID : Computes columnEncoding UnaryBinary.unaryEncoding (fun c : Column => c.1) := Wiring.firstComputes _ _
def body := Wiring.secondComputes UnaryBinary.unaryEncoding (pairEncoding RawClosedNetwork.vertexEncoding encodingNatBool)
def record : Computes columnEncoding RawClosedNetwork.vertexEncoding (fun c : Column => c.2.1) :=
  body.andThen (Wiring.firstComputes _ _)
def wordID : Computes columnEncoding encodingNatBool (fun c : Column => c.2.2) := body.andThen (Wiring.secondComputes _ _)
def label : Computes columnEncoding encodingNatBool (fun c : Column => c.2.1.1) :=
  record.andThen (recode (Wiring.firstComputes encodingNatBool (framedListEncoding RawClosedNetwork.endpointEncoding))
    id (fun _ => rfl) (fun _ => rfl))
def ports : Computes columnEncoding (framedListEncoding RawClosedNetwork.endpointEncoding) (fun c : Column => c.2.1.2) :=
  record.andThen (recode (Wiring.secondComputes encodingNatBool (framedListEncoding RawClosedNetwork.endpointEncoding))
    id (fun _ => rfl) (fun _ => rfl))

def indexedEncoding := pairEncoding columnEncoding UnaryBinary.unaryEncoding
def normalization (x : Column × ℕ) : ℤ := if x.1.1 = x.2 then 1 else 0
def normalizationComputes : Computes indexedEncoding IntegerArithmetic.encoding normalization := by
  let col := Wiring.firstComputes columnEncoding UnaryBinary.unaryEncoding
  let v := Wiring.secondComputes columnEncoding UnaryBinary.unaryEncoding
  refine congrComputes (ifComputes ((pairComputes (col.andThen vertexID) v).andThen
    TraversalCompletion.RationalLP.Parsing.unaryEqual)
    (constantComputes indexedEncoding IntegerArithmetic.encoding 1)
    (constantComputes indexedEncoding IntegerArithmetic.encoding 0)) ?_
  intro x
  simp only [Function.comp_apply, normalization, decide_eq_true_eq]

def zeroEntry (D : Source.Family s arity) (c : Column) : Bool :=
  FiniteDispatch.select (fun c : Column => c.2.1.1)
    (fun c i => FiniteDispatch.select (fun c : Column => c.2.2)
      (fun _ k => decide (D.signatures i (localWord (arity := arity) i k) = 0))
      (fun _ => false) (List.finRange (localCount (arity := arity) i)) c)
    (fun _ => false) (List.finRange s) c

def zeroComputes (D : Source.Family s arity) : Computes columnEncoding encodingBoolBool (zeroEntry D) :=
  FiniteDispatch.computes columnEncoding encodingBoolBool _ _ _ label
    (fun i => FiniteDispatch.computes columnEncoding encodingBoolBool _ _ _ wordID
      (fun k => constantComputes columnEncoding encodingBoolBool
        (decide (D.signatures i (localWord (arity := arity) i k) = 0)))
      (constantComputes columnEncoding encodingBoolBool false) (List.finRange (localCount (arity := arity) i)))
    (constantComputes columnEncoding encodingBoolBool false) (List.finRange s)

def edgeLocal (i : Fin s) (k : Fin (localCount (arity := arity) i)) (x : Column × ℕ) : ℤ :=
  ((List.finRange (arity i.val)).map (fun j =>
    if (x.1.2.1.2.getD j.val (0, false)).1 = x.2 then LinearSystem.spinZ (localWord i k j) else 0)).sum

def edge (x : Column × ℕ) : ℤ :=
  FiniteDispatch.select (fun x : Column × ℕ => x.1.2.1.1)
    (fun x i => FiniteDispatch.select (fun x : Column × ℕ => x.1.2.2)
      (fun x k => edgeLocal (arity := arity) i k x) (fun _ => 0)
      (List.finRange (localCount (arity := arity) i)) x)
    (fun _ => 0) (List.finRange s) x

def sumFixed {A J : Type} (ea : Encoding A Bool) (f : J → A → ℤ)
    (cell : ∀ j, Computes ea IntegerArithmetic.encoding (f j)) :
    (js : List J) → Computes ea IntegerArithmetic.encoding (fun a => (js.map (fun j => f j a)).sum)
  | [] => constantComputes ea IntegerArithmetic.encoding 0
  | j :: js => congrComputes
      ((pairComputes (cell j) (sumFixed ea f cell js)).andThen RationalArithmetic.integerAdditionComputes)
      (fun _ => rfl)

def edgeLocalComputes (i : Fin s) (k : Fin (localCount (arity := arity) i)) :
    Computes indexedEncoding IntegerArithmetic.encoding (edgeLocal (arity := arity) i k) := by
  let col := Wiring.firstComputes columnEncoding UnaryBinary.unaryEncoding
  let e := (Wiring.secondComputes columnEncoding UnaryBinary.unaryEncoding).andThen UnaryBinary.computes
  refine sumFixed indexedEncoding _ ?_ (List.finRange (arity i.val))
  intro j
  let ep := (col.andThen ports).andThen (getDComputes RawClosedNetwork.endpointEncoding j.val (0, false))
  let eid := ep.andThen ProductMachine.Endpoint.edgeComputes
  refine congrComputes (ifComputes (AccessPrograms.eqNat eid e)
    (constantComputes indexedEncoding IntegerArithmetic.encoding (LinearSystem.spinZ (localWord i k j)))
    (constantComputes indexedEncoding IntegerArithmetic.encoding 0)) ?_
  intro x
  simp only [Function.comp_apply, id_eq, decide_eq_true_eq]

def edgeComputes : Computes indexedEncoding IntegerArithmetic.encoding (edge (s := s) (arity := arity)) := by
  let col := Wiring.firstComputes columnEncoding UnaryBinary.unaryEncoding
  exact FiniteDispatch.computes indexedEncoding IntegerArithmetic.encoding _ _ _ (col.andThen label)
    (fun i => FiniteDispatch.computes indexedEncoding IntegerArithmetic.encoding _ _ _ (col.andThen wordID)
      (fun k => edgeLocalComputes i k) (constantComputes indexedEncoding IntegerArithmetic.encoding 0)
      (List.finRange (localCount (arity := arity) i)))
    (constantComputes indexedEncoding IntegerArithmetic.encoding 0) (List.finRange s)

def diagonal (D : Source.Family s arity) (x : Column × Column) : ℤ :=
  if zeroEntry D x.1 && decide (x.1.1 = x.2.1) && decide (x.1.2.2 = x.2.2.2) then 1 else 0

def diagonalComputes (D : Source.Family s arity) :
    Computes (pairEncoding columnEncoding columnEncoding) IntegerArithmetic.encoding (diagonal D) := by
  let a := Wiring.firstComputes columnEncoding columnEncoding
  let b := Wiring.secondComputes columnEncoding columnEncoding
  let veq := (pairComputes (a.andThen vertexID) (b.andThen vertexID)).andThen TraversalCompletion.RationalLP.Parsing.unaryEqual
  let weq := AccessPrograms.eqNat (a.andThen wordID) (b.andThen wordID)
  exact ifComputes (AccessPrograms.bool Bool.and (AccessPrograms.bool Bool.and (a.andThen (zeroComputes D)) veq) weq)
    (constantComputes _ IntegerArithmetic.encoding 1) (constantComputes _ IntegerArithmetic.encoding 0)

end
end Holant.LocalDrafts.Tractability.EOEvaluation.MatrixCells
