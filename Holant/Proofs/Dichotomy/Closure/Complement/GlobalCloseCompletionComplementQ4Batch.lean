import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ChainCompilerSemantics
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4NodeMachine
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4IterationMachine
import Holant.Proofs.Algorithms.TraceQueryControl
import Holant.Complexity.BinaryInterpolation.DivisionStack

/-! Concrete preprocessing and postprocessing for both spectral recoveries.
Four physical unary loops emit the roots, actual native chains emit the query
list, and the retained context contains only the roots and target value. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Batch
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
namespace C
export GlobalCloseCompletionComplementQ4ChainCompilerSemantics
  (Source sourceEncoding query queryComputes arity)
end C
namespace M
export GlobalCloseCompletionComplementQ4NodeMachine (roots computes)
end M
namespace I
export GlobalCloseCompletionComplementQ4IterationMachine (State stateEncoding finite step)
end I
namespace W
export Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WireLists
  (lengthComputes succComputes tabulate append getD)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {degree s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (a i.val))
variable (N : NativeAntiTargetSource.Output H 4) (v : Fin 4→K) (support : Bool) (j : Fin 4)

abbrev Input:=C.Source H N
abbrev inputEncoding:=C.sourceEncoding H N
abbrev queryEncoding:=RawClosedNetwork.validatedEncoding s 1 a
abbrev Context:=List K×K
abbrev contextEncoding:=pairEncoding (framedListEncoding F.encoding) F.encoding
abbrev answerEncoding:=OracleBatch.contextEncoding F.encoding (contextEncoding F)
abbrev oldTables:=NativeAntiTargetSource.base H F
abbrev count (x : Input H N):=Holant.Complexity.FixedGadgetSubstitution.occurrences s x.val

def roots (x : Input H N):=M.roots v support j (count H N x)
def target (x : Input H N):=if support then (0:K) else v j^count H N x
def sampleCount (x : Input H N):=(roots H N v support j x).length+(if support then 0 else 1)
def queries (x : Input H N):=(List.range (sampleCount H N v support j x)).map (fun k=>C.query H N (x,k))
def context (x : Input H N):=(roots H N v support j x,target H N v support j x)
def preprocessing (x : Input H N):=(queries H N v support j x,context H N v support j x)

def countComputes : Computes (inputEncoding H N) UnaryBinary.unaryEncoding (count H N):=
  Compiler.occurrencesComputes (s+1) 1 (C.arity H N) s
def rootsComputes : Computes (inputEncoding H N) (framedListEncoding F.encoding) (roots H N v support j):=
  (countComputes H N).andThen (M.computes F v support j)
def targetComputes : Computes (inputEncoding H N) F.encoding (target H N v support j) := by
  cases support
  · exact congrComputes ((countComputes H N).andThen (ScalarPower.computes F (F.decode.symm (v j))))
      (fun x=>by simp [target])
  · exact constantComputes (inputEncoding H N) F.encoding 0

def sampleCountComputes : Computes (inputEncoding H N) UnaryBinary.unaryEncoding (sampleCount H N v support j) := by
  let length:=(rootsComputes F H N v support j).andThen (W.lengthComputes F.encoding)
  cases support
  · exact congrComputes (length.andThen W.succComputes) (fun x=>by simp [sampleCount])
  · exact congrComputes length (fun x=>by simp [sampleCount])
def queriesComputes : Computes (inputEncoding H N) (framedListEncoding (queryEncoding (s:=s) (a:=a)))
    (queries H N v support j):=
  W.tabulate (inputEncoding H N) (queryEncoding (s:=s) (a:=a)) _
    (sampleCountComputes F H N v support j) (fun x k=>C.query H N (x,k)) (C.queryComputes H N)
def contextComputes : Computes (inputEncoding H N) (contextEncoding F) (context H N v support j):=
  pairComputes (rootsComputes F H N v support j) (targetComputes F H N v support j)
def pre : Computes (inputEncoding H N)
    (OracleBatch.contextEncoding (queryEncoding (s:=s) (a:=a)) (contextEncoding F))
    (preprocessing H N v support j):=
  pairComputes (queriesComputes F H N v support j) (contextComputes F H N v support j)

def prepare (z : List K×Context (K:=K)) : List K×I.State (K:=K):=
  (z.2.1,((if support then 0::z.1 else z.1),(z.2.2,if support then 1 else z.2.2)))
def prepareComputes : Computes (answerEncoding F)
    (ReverseFold.inputEncoding F.encoding (I.stateEncoding F)) (prepare (K:=K) support) := by
  let answers:=Wiring.firstComputes (framedListEncoding F.encoding) (contextEncoding F)
  let ctx:=Wiring.secondComputes (framedListEncoding F.encoding) (contextEncoding F)
  let roots:=ctx.andThen (Wiring.firstComputes (framedListEncoding F.encoding) F.encoding)
  let target:=ctx.andThen (Wiring.secondComputes (framedListEncoding F.encoding) F.encoding)
  cases support
  · exact pairComputes roots (pairComputes answers (pairComputes target target))
  · let values:=(pairComputes (constantComputes (answerEncoding F) (framedListEncoding F.encoding) [0]) answers).andThen (W.append F.encoding)
    exact pairComputes roots (pairComputes values (pairComputes target (constantComputes (answerEncoding F) F.encoding 1)))

def finish (state : I.State (K:=K)) : K:=
  (if support then -state.1.getD 0 0 else state.1.getD 0 0)/state.2.2
def finishComputes : Computes (I.stateEncoding F) F.encoding (finish (K:=K) support) := by
  let values:=Wiring.firstComputes (framedListEncoding F.encoding) (pairEncoding F.encoding F.encoding)
  let head:=(pairComputes values (constantComputes (I.stateEncoding F) UnaryBinary.unaryEncoding 0)).andThen (W.getD F.encoding (0:K))
  let payload:=Wiring.secondComputes (framedListEncoding F.encoding) (pairEncoding F.encoding F.encoding)
  let denom:=payload.andThen (Wiring.secondComputes F.encoding F.encoding)
  cases support
  · exact (pairComputes head denom).andThen (fieldDivisionComputes F)
  · let negative:=(pairComputes (constantComputes (I.stateEncoding F) F.encoding (-1:K)) head).andThen (Concrete.fieldMultiplication F)
    exact congrComputes ((pairComputes negative denom).andThen (fieldDivisionComputes F)) (fun z=>by simp [finish])

def post:= (prepareComputes F support).machine.compose ((I.finite F).machine.compose (finishComputes F support).machine)
def machine:=OracleBatch.machine (pre F H N v support j).machine (post F support)
def answered (x : Input H N):=OracleBatch.answers ((oldTables F H).evaluate F) (preprocessing H N v support j x)
def initial (x : Input H N):=prepare support (answered F H N v support j x)
def resultState (x : Input H N):=(initial F H N v support j x).1.foldr I.step (initial F H N v support j x).2
def result (x : Input H N):=finish support (resultState F H N v support j x)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Batch
end
