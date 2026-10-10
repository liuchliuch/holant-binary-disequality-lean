import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanControl
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScanFinish
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborPredicateSpec
import Holant.Complexity.GraphPreprocessing.ParentRowEncoding

namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048
set_option Elab.async false

abbrev actual := NeighborPredicate.machine
local instance : DecidableEq actual.K := actual.decidableK
local instance : DecidableEq (Stack actual) := (machine actual).decidableK

def edgeBits {n : ℕ} (edges : List (Fin n × Fin n)) : List Bool :=
  ReachRound.encode (edges.map fun e => (e.1.val,e.2.val))

@[simp] theorem edgeBits_nil {n : ℕ} : edgeBits ([] : List (Fin n × Fin n)) = [] := rfl
@[simp] theorem edgeBits_cons {n : ℕ} (u v : Fin n) (edges : List (Fin n × Fin n)) :
    edgeBits ((u,v)::edges) = ReachRound.unary u.val++ReachRound.unary v.val++edgeBits edges := by simp [edgeBits]

def predicate (table : List Bool) (target endpoint opposite : Fin table.length) : Bool :=
  decide (target=endpoint) && table.get opposite

def searchFrom (table : List Bool) (target : Fin table.length) : ℕ → List (Fin table.length × Fin table.length) → Option (ℕ × Bool)
  | _, [] => none
  | index, (u,v)::rest => if predicate table target u v then some (index,false)
      else if predicate table target v u then some (index,true) else searchFrom table target (index+1) rest

noncomputable def callTime (table : List Bool) (target endpoint opposite : Fin table.length) : ℕ :=
  let x := NeighborPredicate.query table target endpoint opposite
  (NeighborPredicate.timed x).steps+2*(NeighborPredicate.inputEncoding.encode x).length+12

noncomputable def callBound (N : ℕ) : ℕ := NeighborPredicate.timePolynomial.eval (9*(N+1))+18*(N+1)+12
noncomputable def roundBound (N : ℕ) : ℕ := 2*callBound N+30*(N+1)

theorem callTime_le (table : List Bool) (target endpoint opposite : Fin table.length) (N : ℕ) (hB : table.length≤N) :
    callTime table target endpoint opposite ≤ callBound N := by
  let x := NeighborPredicate.query table target endpoint opposite
  have hs := (NeighborPredicate.timed x).steps_le_m
  have hw : (NeighborPredicate.inputEncoding.encode x).length ≤ 9*(N+1) :=
    le_trans (NeighborPredicate.query_length table target endpoint opposite) (by omega)
  have hp := natPolynomial_eval_mono NeighborPredicate.timePolynomial hw
  unfold callTime callBound
  dsimp only [x] at *
  omega

theorem call_test (table : List Bool) (target endpoint opposite : Fin table.length)
    (input index side output : List Bool) :
    RunsExactly (TM2.step (program actual))
      (ready actual (.inl (.inr 0)) table (List.replicate target.val true)
        (List.replicate endpoint.val true) (List.replicate opposite.val true) input index side output)
      (config actual (.inr 7) (wordTape actual.output [predicate table target endpoint opposite]) table
        (List.replicate target.val true) (List.replicate endpoint.val true) (List.replicate opposite.val true)
        [] [] [] input index [] side output)
      (callTime table target endpoint opposite) := by
  let x := NeighborPredicate.query table target endpoint opposite
  have h := call_exact actual table (List.replicate target.val true) (List.replicate endpoint.val true)
    (List.replicate opposite.val true) input index side output
    (encodingBoolBool.encode (NeighborPredicate.value x)) (NeighborPredicate.timed x).steps
    (NeighborPredicate.timed x).evals_in_steps
  have hx : NeighborPredicate.value x = predicate table target endpoint opposite :=
    NeighborPredicate.query_value table target endpoint opposite
  have hout : encodingBoolBool.encode (NeighborPredicate.value x) = [predicate table target endpoint opposite] := by
    simp [hx,encodingBoolBool,encodeBool]
  have hw : NeighborPredicate.inputEncoding.encode x = NeighborCall.queryWord table
      (List.replicate target.val true) (List.replicate endpoint.val true) (List.replicate opposite.val true) := rfl
  simpa only [ready,callTime,← hw,hout] using h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.NeighborScan
