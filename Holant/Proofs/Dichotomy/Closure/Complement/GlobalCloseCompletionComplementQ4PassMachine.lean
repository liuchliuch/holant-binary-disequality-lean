import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Differences
import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Complexity.FixedFieldMachines.Concrete

/-! A real fixed-field machine for one shrinking difference pass. It uses
the existing framed-list access and contextual traversal machines, with
ordinary field multiplication/addition on the unchanged coefficient codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4PassMachine
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing
namespace W
export Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.WireLists
  (lengthComputes succComputes tabulate)
end W
namespace A
export Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.AccessPrograms (get)
end A
namespace E
export Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Endpoints (unaryPredecessorComputes)
end E
namespace D
export GlobalCloseCompletionComplementQ4Differences (pass)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {degree : ℕ}
variable (F : FixedField K degree)

def inputEncoding:=pairEncoding F.encoding (framedListEncoding F.encoding)
def cellEncoding:=pairEncoding (inputEncoding F) UnaryBinary.unaryEncoding
def mappedPass (node : K) (values : List K) : List K:=
  (List.range (values.length-1)).map (fun i=>values.getD (i+1) 0-node*values.getD i 0)

theorem mappedPass_eq (node : K) (values : List K) : mappedPass node values=D.pass node values := by
  induction values with
  | nil=>rfl
  | cons a values ih=>
    cases values with
    | nil=>rfl
    | cons b values=>
      simp only [mappedPass,List.length_cons,Nat.add_sub_cancel,List.range_succ_eq_map,
        List.map_cons,List.map_map,List.getD_cons_zero,List.getD_cons_succ,D.pass]
      congr 1

def context : Computes (cellEncoding F) (inputEncoding F) (fun x : (K×List K)×ℕ=>x.1):=
  Wiring.firstComputes (inputEncoding F) UnaryBinary.unaryEncoding
def index : Computes (cellEncoding F) UnaryBinary.unaryEncoding (fun x : (K×List K)×ℕ=>x.2):=
  Wiring.secondComputes (inputEncoding F) UnaryBinary.unaryEncoding
def values : Computes (cellEncoding F) (framedListEncoding F.encoding) (fun x : (K×List K)×ℕ=>x.1.2):=
  (context F).andThen (Wiring.secondComputes F.encoding (framedListEncoding F.encoding))
def node : Computes (cellEncoding F) F.encoding (fun x : (K×List K)×ℕ=>x.1.1):=
  (context F).andThen (Wiring.firstComputes F.encoding (framedListEncoding F.encoding))
def left : Computes (cellEncoding F) F.encoding (fun x : (K×List K)×ℕ=>x.1.2.getD x.2 0):=
  A.get F.encoding 0 (values F) (index F)
def right : Computes (cellEncoding F) F.encoding (fun x : (K×List K)×ℕ=>x.1.2.getD (x.2+1) 0):=
  A.get F.encoding 0 (values F) ((index F).andThen W.succComputes)

def cell : Computes (cellEncoding F) F.encoding
    (fun x : (K×List K)×ℕ=>x.1.2.getD (x.2+1) 0-x.1.1*x.1.2.getD x.2 0) := by
  let product:=(pairComputes (node F) (left F)).andThen (Concrete.fieldMultiplication F)
  let negative:=(pairComputes (constantComputes (cellEncoding F) F.encoding (-1:K)) product).andThen
    (Concrete.fieldMultiplication F)
  exact congrComputes ((pairComputes (right F) negative).andThen (Concrete.fieldAddition F))
    (fun x=>by simp only [Function.comp_apply,neg_one_mul,sub_eq_add_neg])

def count : Computes (inputEncoding F) UnaryBinary.unaryEncoding
    (fun x : K×List K=>x.2.length-1):=
  ((Wiring.secondComputes F.encoding (framedListEncoding F.encoding)).andThen
    (W.lengthComputes F.encoding)).andThen E.unaryPredecessorComputes

def computes : Computes (inputEncoding F) (framedListEncoding F.encoding)
    (fun x : K×List K=>D.pass x.1 x.2):=
  congrComputes (W.tabulate (inputEncoding F) F.encoding (fun x : K×List K=>x.2.length-1)
    (count F) (fun x i=>x.2.getD (i+1) 0-x.1*x.2.getD i 0) (cell F))
    (fun x=>mappedPass_eq x.1 x.2)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4PassMachine
end
