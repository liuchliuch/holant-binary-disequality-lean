import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4PassMachine
import Holant.Proofs.LinearProgramming.Support.Infrastructure.Fold

/-! The actual outer difference controller carries its sample list, target
and denominator in framed field words. The existing finite reverse fold
runs the constructed pass machine. Polynomial timing is supplied separately
from proved bounds on these particular arithmetic states, not inferred from
iteration of a polynomial one-step bound. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4IterationMachine
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure
namespace P
export GlobalCloseCompletionComplementQ4PassMachine (computes)
end P
namespace D
export GlobalCloseCompletionComplementQ4Differences (pass factor processList)
end D
namespace R
export Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.ReverseFold
  (inputEncoding encoding start step iterate_start computes)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {degree : ℕ}
variable (F : FixedField K degree)

abbrev State:=List K×(K×K)
def stateEncoding:=pairEncoding (framedListEncoding F.encoding) (pairEncoding F.encoding F.encoding)
def cellEncoding:=pairEncoding F.encoding (stateEncoding F)
def step (root : K) (state : State (K:=K)) : State (K:=K):=
  (D.pass root state.1,(state.2.1,state.2.2*(state.2.1-root)))

def state : Computes (cellEncoding F) (stateEncoding F) (fun x : K×State (K:=K)=>x.2):=
  Wiring.secondComputes F.encoding (stateEncoding F)
def root : Computes (cellEncoding F) F.encoding (fun x : K×State (K:=K)=>x.1):=
  Wiring.firstComputes F.encoding (stateEncoding F)
def values : Computes (cellEncoding F) (framedListEncoding F.encoding) (fun x : K×State (K:=K)=>x.2.1):=
  (state F).andThen (Wiring.firstComputes (framedListEncoding F.encoding) (pairEncoding F.encoding F.encoding))
def payload : Computes (cellEncoding F) (pairEncoding F.encoding F.encoding) (fun x : K×State (K:=K)=>x.2.2):=
  (state F).andThen (Wiring.secondComputes (framedListEncoding F.encoding) (pairEncoding F.encoding F.encoding))
def target : Computes (cellEncoding F) F.encoding (fun x : K×State (K:=K)=>x.2.2.1):=
  (payload F).andThen (Wiring.firstComputes F.encoding F.encoding)
def denominator : Computes (cellEncoding F) F.encoding (fun x : K×State (K:=K)=>x.2.2.2):=
  (payload F).andThen (Wiring.secondComputes F.encoding F.encoding)

def difference : Computes (cellEncoding F) F.encoding (fun x : K×State (K:=K)=>x.2.2.1-x.1) := by
  let negative:=(pairComputes (constantComputes (cellEncoding F) F.encoding (-1:K)) (root F)).andThen
    (Concrete.fieldMultiplication F)
  exact congrComputes ((pairComputes (target F) negative).andThen (Concrete.fieldAddition F))
    (fun x=>by simp only [Function.comp_apply,neg_one_mul,sub_eq_add_neg])

def cell : Computes (cellEncoding F) (stateEncoding F) (fun x : K×State (K:=K)=>step x.1 x.2):=
  pairComputes ((pairComputes (root F) (values F)).andThen (P.computes F))
    (pairComputes (target F) ((pairComputes (denominator F) (difference F)).andThen (Concrete.fieldMultiplication F)))

def finite : FiniteComputes (R.inputEncoding F.encoding (stateEncoding F)) (stateEncoding F)
    (fun x : List K×State (K:=K)=>x.1.foldr step x.2):=
  R.computes F.encoding (stateEncoding F) (0:K) step (FiniteComputes.ofPoly (cell F))

theorem fold_value (roots : List K) (s : State (K:=K)) :
    roots.foldr step s=(roots.foldr D.pass s.1,(s.2.1,s.2.2*D.factor roots s.2.1)) := by
  induction roots with
  | nil=>simp [D.factor]
  | cons root roots ih=>
    rw [List.foldr_cons,ih]
    simp only [step,D.factor,List.map_cons,List.prod_cons,List.foldr_cons]
    congr 2
    ring

theorem values_reverse (roots values : List K) :
    roots.foldr D.pass values=D.processList roots.reverse values := by
  simp only [D.processList,List.foldl_reverse]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4IterationMachine
end
