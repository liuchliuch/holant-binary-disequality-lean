import Holant.Proofs.Traversal.ArityTwo.RawSeedSelection
import Holant.Proofs.Traversal.ArityTwo.WalkCodeExpansion
import Holant.Proofs.Traversal.ArityTwo.FixedField
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.BranchDriver


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawBytecodeMachine
open Holant Holant.Complexity Computability Holant.OneHot.StackProgram
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open UniversalPairReduction.SmoothingCompiler
open Holant.OneHot.StackProgram.GraphLabelEncoding
noncomputable section
set_option backward.isDefEq.respectTransparency false

def join (a b : Machine) : Machine := (pairMachine a b).compose WordJoin.machine

variable (s b : ℕ) (arity : ℕ → ℕ) {A : Type}
variable (labels : (i : Fin s) → Signature A (arity i.val))
variable (edges : Fin b → Kernel A) (codec : Encoding A Bool)

def firstEndpoint (x : RawRootReach.Input s b arity) : RawEndpoint :=
  (x.1.val.vertices.get x.2).2.getD 0 (0,false)

def firstEndpointComputes : Computes (RawRootReach.inputEncoding s b arity)
    RawClosedNetwork.endpointEncoding (firstEndpoint s b arity) :=
  ((originalRowComputes s b arity).andThen
    (recode (Wiring.secondComputes encodingNatBool
      (framedListEncoding RawClosedNetwork.endpointEncoding)) id (fun _ => rfl) (fun _ => rfl))).andThen
        (getDComputes RawClosedNetwork.endpointEncoding 0 (0,false))

/-- This preparation is total even at a nullary row. The optional driver only
calls a traversal provider when its actual selected degree is one or two. -/
def endpointWord (opposite : Bool) (x : RawRootReach.Input s b arity) : List Bool :=
  Holant.Algebraic.frame (RawClosedNetwork.encoding.encode x.1.val) ++
    RawClosedNetwork.endpointEncoding.encode
      (if opposite then ((firstEndpoint s b arity x).1,!(firstEndpoint s b arity x).2)
        else firstEndpoint s b arity x)

def endpointWordComputes (opposite : Bool) : Computes (RawRootReach.inputEncoding s b arity)
    Frame.wordEncoding (endpointWord s b arity opposite) := by
  cases opposite with
  | false =>
    exact recode (pairComputes (sourceComputes s b arity) (firstEndpointComputes s b arity))
      id (fun _ => rfl) (fun _ => rfl)
  | true =>
    exact recode (pairComputes (sourceComputes s b arity)
      ((firstEndpointComputes s b arity).andThen RawPortQuery.flipComputes))
      id (fun _ => rfl) (fun _ => rfl)

def dotWordComputes : Computes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding
    (fun x => MatrixEmission.word codec (dotCode (fun bit => labels (sourceLabel s b arity x) (fun _ => bit)))) :=
  labelRecodeComputes s b arity Frame.wordEncoding
    (fun i => MatrixEmission.word codec (dotCode (fun bit => labels i (fun _ => bit))))

def pathMachine : Machine :=
  join
    (join ((endpointWordComputes s b arity true).machine.compose
      (ActionTableCompiler.machine s b arity labels edges codec false []))
      ((endpointWordComputes s b arity false).machine.compose
        (EndpointEmission.computes s b arity edges codec).machine))
    (dotWordComputes s b arity labels codec).machine

def basisWord (bit : Bool) : List Bool :=
  MatrixEmission.word codec (if bit then [.one,.zero] else [.zero,.one])

def columnMachine (bit : Bool) : Machine :=
  join ((endpointWordComputes s b arity false).machine.compose
    (ActionTableCompiler.machine s b arity labels edges codec true (basisWord codec bit)))
    (Constant.machine (MatrixEmission.word codec [if bit then .erase 0 else .erase 1]))

def cycleMachine : Machine :=
  join (join (columnMachine s b arity labels edges codec false)
    (columnMachine s b arity labels edges codec true))
    (Constant.machine (MatrixEmission.word codec [.add]))

def selectedDegree (x : RawRootReach.Input s b arity) : ℕ := PortWalk.degree (arity := arity) x.1.val x.2

def optional (n : ℕ) (x : RawRootReach.Input s b arity) : Option (List Bool) :=
  if selectedDegree s b arity x = n then some ((RawRootReach.inputEncoding s b arity).encode x) else none

def optionalComputes (n : ℕ) : Computes (RawRootReach.inputEncoding s b arity)
    (optionEncoding Frame.wordEncoding) (optional s b arity n) := by
  let present : Computes (RawRootReach.inputEncoding s b arity) (optionEncoding Frame.wordEncoding)
      (fun x => some ((RawRootReach.inputEncoding s b arity).encode x)) :=
    recode (joinComputes
      (constantComputes (RawRootReach.inputEncoding s b arity) Frame.wordEncoding [true])
      (encodeComputes (RawRootReach.inputEncoding s b arity))) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (ifComputes
    (labelRecodeComputes s b arity encodingBoolBool (fun i => decide (arity i.val = n))) present
    (constantComputes (RawRootReach.inputEncoding s b arity) (optionEncoding Frame.wordEncoding) none))
    (fun x => by simp [optional,selectedDegree,PortWalk.degree,sourceLabel])

/-- `OptionMap` invokes its provider only for `some`, unlike the eager fixed
candidate selector. This is required for an empty or nullary input graph. -/
def optionalMachine (n : ℕ) (provider : Machine) : Machine :=
  ((optionalComputes s b arity n).machine.compose (OptionMap.machine provider))

def optionValue (m : Machine) : Machine :=
  (pairMachine m (Constant.machine [false])).compose (OptionChoice.machine [])

def selectedComponentMachine : Machine :=
  join
    (join
      (optionValue (optionalMachine s b arity 0 (MatrixEmission.scalarComputes s b arity labels codec).machine))
      (optionValue (optionalMachine s b arity 1 (pathMachine s b arity labels edges codec))))
    (optionValue (optionalMachine s b arity 2 (cycleMachine s b arity labels edges codec)))

def componentMachine : Machine :=
  (RawSeedSelection.computes s b arity).machine.compose
    (selectedComponentMachine s b arity labels edges codec)

def rootInputEncoding := pairEncoding (RawClosedNetwork.validatedEncoding s b arity)
  ComponentSelection.RawRoots.outputEncoding

def rootsComputes : Computes (RawClosedNetwork.validatedEncoding s b arity) (rootInputEncoding s b arity)
    (fun r => (r,ComponentSelection.RawRoots.value r)) :=
  pairComputes (identityComputes (RawClosedNetwork.validatedEncoding s b arity))
    (ComponentSelection.RawRoots.computes s b arity)

/-- Emit component code in original root order, followed by one and exactly one
multiply for each actual root. This is literally `componentsCode`, including
the empty graph; no varying number is compiled into the finite controller. -/
def compiler : Machine :=
  let start := (rootsComputes s b arity).machine
  let componentWords := start.compose (ContextFlatMap.machine (componentMachine s b arity labels edges codec))
  let multiplyWords := start.compose
    (ContextFlatMap.machine (Constant.machine (MatrixEmission.word codec [.mul])))
  join (join componentWords
    (join (Constant.machine (MatrixEmission.word codec [.one])) multiplyWords))
    (Constant.machine [false])

theorem componentsCode_flat (cs : List (Component A)) :
    componentsCode cs = cs.flatMap Component.code ++ [.one] ++ List.replicate cs.length Op.mul := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [componentsCode,ih]
    simp only [List.flatMap_cons,List.length_cons]
    rw [List.replicate_add]
    simp [List.append_assoc]

variable {K : Type} [Fintype A] [DecidableEq A] [Field K] [Algebra ℚ K] {n : ℕ}

/-- Complete executable wiring. Its sole input tape is the original raw graph
encoding. A global correctness/time theorem is intentionally not claimed yet. -/
def machine (F : Algebraic.FixedField K n) (coords : A → Fin n → ℚ) : Machine :=
  (compiler s b arity labels edges codec).compose (FixedField.machine F coords codec)

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.RawBytecodeMachine
