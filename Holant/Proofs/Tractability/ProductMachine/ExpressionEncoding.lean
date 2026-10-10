import Holant.Proofs.Tractability.ProductMachine.Expression


namespace Holant.LocalDrafts.Tractability.ProductMachine.Expr

open Computability Holant.Complexity Holant.OneHot.StackProgram
variable {A : Type}

def parseStep : Op A → List (Expr A) → Option (List (Expr A))
  | .zero, s => some (.zero :: s)
  | .one, s => some (.one :: s)
  | .literal a, s => some (.literal a :: s)
  | .add, a :: b :: s => some (.add a b :: s)
  | .mul, a :: b :: s => some (.mul a b :: s)
  | _, _ => none

def parse : Code A → List (Expr A) → Option (List (Expr A))
  | [], s => some s
  | op :: ops, s => (parseStep op s).bind (parse ops)

theorem parse_append (a b : Code A) (s : List (Expr A)) :
    parse (a ++ b) s = (parse a s).bind (parse b) := by
  induction a generalizing s with
  | nil => rfl
  | cons op ops ih => simp [parse, ih, Option.bind_assoc]

theorem parse_code (e : Expr A) (s : List (Expr A)) : parse e.code s = some (e :: s) := by
  induction e generalizing s <;> simp_all [code, parse_append, parse, parseStep]

def encoding (labels : Encoding A Bool) : Encoding (Expr A) Bool where
  encode e := (codeEncoding labels).encode e.code
  decode bits := do
    let ops ← (codeEncoding labels).decode bits
    let s ← parse ops []
    match s with
    | [e] => some e
    | _ => none
  decode_encode e := by simp [parse_code]

theorem size_le_encoded (labels : Encoding A Bool) (e : Expr A) :
    e.size ≤ ((encoding labels).encode e).length := by
  have h := framedListEncoding_length_lower (opEncoding labels) e.code
  rw [code_length] at h
  change e.size ≤ ((framedListEncoding (opEncoding labels)).encode e.code).length
  omega

end Holant.LocalDrafts.Tractability.ProductMachine.Expr
