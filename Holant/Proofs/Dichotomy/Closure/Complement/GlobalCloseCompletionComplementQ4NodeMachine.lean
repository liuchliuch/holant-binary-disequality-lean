import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4PassMachine
import Holant.Complexity.FixedFieldMachines.ScalarPower.Compile
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Combinators

/-! Four literal unary loops emit the spectral monomial-node list in the
original fixed field. Powers use the checked scalar-power machine; guards
compare natural counts, and no algebraic equality oracle or code generator
is supplied. The support mode pads invalid tuples by one, the single-mode
projection mode by zero and also omits its pure target tuple. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4NodeMachine
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution.Compiler
namespace W
export Holant.Complexity.BinaryInterpolation.WeightCompiler (unary successorComputes rangeWordsComputes)
end W
namespace M
export Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators (ifComputes unaryEqual)
export Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.AccessPrograms (unaryAdd)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option maxRecDepth 32768
set_option Elab.async false

abbrev C0:=ℕ
abbrev C1:=C0×ℕ
abbrev C2:=C1×ℕ
abbrev C3:=C2×ℕ
abbrev C4:=C3×ℕ
abbrev e0:=W.unary
abbrev e1:=pairEncoding e0 W.unary
abbrev e2:=pairEncoding e1 W.unary
abbrev e3:=pairEncoding e2 W.unary
abbrev e4:=pairEncoding e3 W.unary

def origin0 : Computes e0 W.unary (fun x : C0=>x):=identityComputes _
def origin1 : Computes e1 W.unary (fun x : C1=>x.1):=Wiring.firstComputes _ _
def origin2 : Computes e2 W.unary (fun x : C2=>x.1.1):=(Wiring.firstComputes e1 W.unary).andThen origin1
def origin3 : Computes e3 W.unary (fun x : C3=>x.1.1.1):=(Wiring.firstComputes e2 W.unary).andThen origin2
def origin4 : Computes e4 W.unary (fun x : C4=>x.1.1.1.1):=(Wiring.firstComputes e3 W.unary).andThen origin3

def coordinates (x : C4) : Fin 4→ℕ:=![x.1.1.1.2,x.1.1.2,x.1.2,x.2]
def exponent0 : Computes e4 W.unary (fun x=>coordinates x 0):=
  ((Wiring.firstComputes e3 W.unary).andThen (Wiring.firstComputes e2 W.unary)).andThen
    ((Wiring.firstComputes e1 W.unary).andThen (Wiring.secondComputes e0 W.unary))
def exponent1 : Computes e4 W.unary (fun x=>coordinates x 1):=
  ((Wiring.firstComputes e3 W.unary).andThen (Wiring.firstComputes e2 W.unary)).andThen
    (Wiring.secondComputes e1 W.unary)
def exponent2 : Computes e4 W.unary (fun x=>coordinates x 2):=
  (Wiring.firstComputes e3 W.unary).andThen (Wiring.secondComputes e2 W.unary)
def exponent3 : Computes e4 W.unary (fun x=>coordinates x 3):=
  Wiring.secondComputes e3 W.unary
def exponent (i : Fin 4) : Computes e4 W.unary (fun x=>coordinates x i) :=
  Fin.cases exponent0 (fun i=>Fin.cases exponent1 (fun i=>Fin.cases exponent2
    (fun i=>Fin.cases exponent3 (fun i=>Fin.elim0 i) i) i) i) i

def total (x : C4) : ℕ:=coordinates x 0+coordinates x 1+coordinates x 2+coordinates x 3
def totalComputes : Computes e4 W.unary total:=
  (pairComputes ((pairComputes ((pairComputes (exponent 0) (exponent 1)).andThen M.unaryAdd)
    (exponent 2)).andThen M.unaryAdd) (exponent 3)).andThen M.unaryAdd
def totalEqual : Computes e4 encodingBoolBool (fun x : C4=>decide (total x=x.1.1.1.1)):=
  (pairComputes totalComputes origin4).andThen M.unaryEqual
def pureEqual (j : Fin 4) : Computes e4 encodingBoolBool
    (fun x : C4=>decide (coordinates x j=x.1.1.1.1)):=
  (pairComputes (exponent j) origin4).andThen M.unaryEqual

variable {K : Type} [Field K] [Algebra ℚ K] {degree : ℕ}
variable (F : FixedField K degree) (v : Fin 4→K)

def power (i : Fin 4) : Computes e4 F.encoding (fun x=>(v i)^(coordinates x i)):=
  (exponent i).andThen (congrComputes (ScalarPower.computes F (F.decode.symm (v i)))
    (fun k=>by rw [LinearEquiv.apply_symm_apply]))
def product (x : C4) : K:=v 0^coordinates x 0*v 1^coordinates x 1*v 2^coordinates x 2*v 3^coordinates x 3
def productComputes : Computes e4 F.encoding (product v):=
  (pairComputes ((pairComputes ((pairComputes (power F v 0) (power F v 1)).andThen
      (Concrete.fieldMultiplication F)) (power F v 2)).andThen (Concrete.fieldMultiplication F))
    (power F v 3)).andThen (Concrete.fieldMultiplication F)

def node (supportMode : Bool) (j : Fin 4) (x : C4) : K:=
  if total x=x.1.1.1.1 then
    if supportMode then product v x else if coordinates x j=x.1.1.1.1 then 0 else product v x
  else if supportMode then 1 else 0

def nodeComputes (supportMode : Bool) (j : Fin 4) : Computes e4 F.encoding (node v supportMode j) := by
  let valid : Computes e4 F.encoding
      (fun x : C4=>if supportMode then product v x else if coordinates x j=x.1.1.1.1 then 0 else product v x) := by
    cases supportMode
    · exact congrComputes (M.ifComputes (pureEqual j) (constantComputes e4 F.encoding (0:K)) (productComputes F v))
        (fun x=>by simp)
    · exact congrComputes (productComputes F v) (fun x=>by simp)
  exact congrComputes (M.ifComputes totalEqual valid
    (constantComputes e4 F.encoding (if supportMode then (1:K) else 0))) (fun x=>by simp [node])

def roots (supportMode : Bool) (j : Fin 4) (n : ℕ) : List K:=
  (List.range (n+1)).flatMap fun a=>(List.range (n+1)).flatMap fun b=>
    (List.range (n+1)).flatMap fun c=>(List.range (n+1)).map fun d=>node v supportMode j ((((n,a),b),c),d)

def entryComputes (supportMode : Bool) (j : Fin 4) : Computes e4 Frame.wordEncoding
    (fun x=>entry F.encoding (node v supportMode j x)):=
  (nodeComputes F v supportMode j).andThen (FixedGadgetSubstitution.Compiler.entryComputes F.encoding)

def loop3 (supportMode : Bool) (j : Fin 4) :=
  W.rangeWordsComputes e3 (fun x : C3=>x.1.1.1+1) (origin3.andThen W.successorComputes)
    (fun x=>entry F.encoding (node v supportMode j x)) (entryComputes F v supportMode j)
def loop2 (supportMode : Bool) (j : Fin 4) :=
  W.rangeWordsComputes e2 (fun x : C2=>x.1.1+1) (origin2.andThen W.successorComputes)
    _ (loop3 F v supportMode j)
def loop1 (supportMode : Bool) (j : Fin 4) :=
  W.rangeWordsComputes e1 (fun x : C1=>x.1+1) (origin1.andThen W.successorComputes)
    _ (loop2 F v supportMode j)
def loop0 (supportMode : Bool) (j : Fin 4) :=
  W.rangeWordsComputes e0 (fun x : C0=>x+1) (origin0.andThen W.successorComputes)
    _ (loop1 F v supportMode j)

def computes (supportMode : Bool) (j : Fin 4) : Computes W.unary (framedListEncoding F.encoding) (roots v supportMode j) := by
  refine recode (joinComputes (loop0 F v supportMode j)
    (constantComputes W.unary Frame.wordEncoding [false])) id (fun _=>rfl) ?_
  intro n
  have last:=entries_append_encode F.encoding (roots v supportMode j n) []
  simpa only [roots,entries,List.flatMap_map,List.flatMap_assoc,List.append_nil,framedListEncoding,
    framedListEncode,Frame.wordEncoding,id_eq] using last


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4NodeMachine
end
