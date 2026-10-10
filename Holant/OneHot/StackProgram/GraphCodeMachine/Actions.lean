import Holant.OneHot.StackProgram.Machine.Dispatch
import Holant.Complexity.FixedFieldMachines.Constant

/-! Finite pending actions and literal record prefixes for the tree compiler. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine
open Computability Holant.Complexity
variable {A : Type}

inductive Action (A : Type) where
  | tree | forest | closed | emit (op : Op A)
  deriving Fintype

def actionEncode (e : Encoding A Bool) : Action A → List Bool
  | .tree => [false, false]
  | .forest => [false, true]
  | .closed => [true, false]
  | .emit op => [true, true] ++ opEncode e op

def actionDecode (e : Encoding A Bool) : List Bool → Option (Action A)
  | [false, false] => some .tree
  | [false, true] => some .forest
  | [true, false] => some .closed
  | true :: true :: rest => (opDecode e rest).map .emit
  | _ => none

@[simp] theorem actionDecode_encode (e : Encoding A Bool) (a : Action A) :
    actionDecode e (actionEncode e a) = some a := by
  cases a <;> simp [actionEncode, actionDecode]

def actionEncoding (e : Encoding A Bool) : Encoding (Action A) Bool where
  encode := actionEncode e
  decode := actionDecode e
  decode_encode := actionDecode_encode e

def workEncoding (e : Encoding A Bool) : Encoding (List (Action A)) Bool :=
  framedListEncoding (actionEncoding e)

def records {X : Type} (e : Encoding X Bool) (xs : List X) : List Bool :=
  xs.flatMap (fun x => true :: Holant.Algebraic.frame (e.encode x))

@[simp] theorem records_append {X : Type} (e : Encoding X Bool) (xs ys : List X) :
    records e (xs ++ ys) = records e xs ++ records e ys := by simp [records]

theorem framedList_records {X : Type} (e : Encoding X Bool) (xs : List X) :
    framedListEncode e xs = records e xs ++ [false] := by
  induction xs <;> simp [framedListEncode, records, List.append_assoc, *]

theorem code_records (e : Encoding A Bool) (code : Code A) :
    (codeEncoding e).encode code = records (opEncoding e) code ++ [false] := framedList_records _ _

theorem work_records (e : Encoding A Bool) (actions : List (Action A)) :
    (workEncoding e).encode actions = records (actionEncoding e) actions ++ [false] := framedList_records _ _

theorem work_prepend (e : Encoding A Bool) (actions pending : List (Action A)) :
    (workEncoding e).encode (actions ++ pending) =
      records (actionEncoding e) actions ++ (workEncoding e).encode pending := by
  simp only [work_records, records_append, List.append_assoc]

theorem actionEncode_length_le (e : Encoding A Bool) (C : ℕ)
    (hlabels : ∀ a, (e.encode a).length ≤ C) (a : Action A) :
    (actionEncode e a).length ≤ C + 8 := by
  cases a with
  | tree | forest | closed => simp [actionEncode]
  | emit op =>
    have h := opEncode_length_le e C hlabels op
    simp only [actionEncode, List.length_append, List.length_cons, List.length_nil]
    omega

def nodeTasks (a b : A) : List (Action A) := .forest :: (nodeCode a b).map .emit
def consTasks (p : A) : List (Action A) := .tree :: .forest :: (consCode p).map .emit
def closedTasks (a : A) : List (Action A) := .forest :: (rootCode a).map .emit

@[simp] theorem nodeTasks_length (a b : A) : (nodeTasks a b).length = 12 := rfl
@[simp] theorem consTasks_length (p : A) : (consTasks p).length = 21 := rfl
@[simp] theorem closedTasks_length (a : A) : (closedTasks a).length = 4 := rfl

end Holant.OneHot.StackProgram.GraphCodeMachine
