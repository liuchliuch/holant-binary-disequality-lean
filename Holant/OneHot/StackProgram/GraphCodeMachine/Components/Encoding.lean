import Holant.OneHot.StackProgram.GraphCodeMachine.Interface
import Holant.OneHot.StackProgram.GraphCodeMachine.JoinCode

/-! Prepared component descriptors retain finite coefficient labels literally.
Every closed tree is separately framed; the surrounding component list is the
existing framed-list protocol. This is an explicit prepared-data boundary. -/
namespace Holant.OneHot.StackProgram.GraphCodeMachine.Components
open Computability Holant.Complexity
variable {A : Type}

inductive Descriptor (A : Type) where
  | dense
  | tree (root : A) (children : Forest A)
  | unicycle (leftRoot : A) (leftChildren : Forest A) (rightRoot : A) (rightChildren : Forest A)

def encode (e : Encoding A Bool) : Descriptor A → List Bool
  | .dense => [false, false]
  | .tree a ts => [false, true] ++ Holant.Algebraic.frame ((closedEncoding e).encode (a, ts))
  | .unicycle a ts b us => [true, false] ++
      Holant.Algebraic.frame ((closedEncoding e).encode (a, ts)) ++
      Holant.Algebraic.frame ((closedEncoding e).encode (b, us))

def decode (e : Encoding A Bool) : List Bool → Option (Descriptor A)
  | [false, false] => some .dense
  | false :: true :: rest => do
    let (word, tail) ← Holant.Algebraic.unframe rest
    if tail ≠ [] then none else
      let (a, ts) ← (closedEncoding e).decode word
      pure (.tree a ts)
  | true :: false :: rest => do
    let (left, tail) ← Holant.Algebraic.unframe rest
    let (right, final) ← Holant.Algebraic.unframe tail
    if final ≠ [] then none else
      let (a, ts) ← (closedEncoding e).decode left
      let (b, us) ← (closedEncoding e).decode right
      pure (.unicycle a ts b us)
  | _ => none

@[simp] theorem decode_encode (e : Encoding A Bool) (d : Descriptor A) :
    decode e (encode e d) = some d := by
  have hf (word : List Bool) : Holant.Algebraic.unframe (Holant.Algebraic.frame word) = some (word, []) := by
    simpa using Holant.Algebraic.unframe_frame_append word []
  cases d <;> simp [encode, decode, Holant.Algebraic.unframe_frame_append, hf,
    (closedEncoding e).decode_encode]

def encoding (e : Encoding A Bool) : Encoding (Descriptor A) Bool where
  encode := encode e
  decode := decode e
  decode_encode := decode_encode e

def listEncoding (e : Encoding A Bool) : Encoding (List (Descriptor A)) Bool :=
  framedListEncoding (encoding e)

def componentCode : Descriptor A → Code A
  | .dense => [.zero]
  | .tree a ts => compileClosed a ts
  | .unicycle a ts b us => addCode (compileClosed a ts) (compileClosed b us)

def productCode : List (Descriptor A) → Code A
  | [] => [.one]
  | d :: ds => mulCode (componentCode d) (productCode ds)

/-- Direct equality to the original finite-product ordering, including empty input. -/
theorem productCode_ofFn {n : ℕ} (d : Fin n → Descriptor A) :
    productCode (List.ofFn d) = finiteProductCode (fun i => componentCode (d i)) := by
  induction n with
  | zero => simp [productCode, finiteProductCode]
  | succ n ih => rw [List.ofFn_succ, productCode, finiteProductCode, ih]

/-- Forward streaming with delayed multiplication has exactly right-fold syntax. -/
theorem productCode_stream (ds : List (Descriptor A)) :
    productCode ds = ds.flatMap componentCode ++ [.one] ++
      (List.replicate ds.length [.swap, .mul]).flatten := by
  induction ds with
  | nil => simp [productCode]
  | cons d ds ih =>
    simp [productCode, mulCode, ih, List.replicate_succ, List.append_assoc]
    have commute (n : ℕ) : (List.replicate n ([.swap, .mul] : Code A)).flatten ++ [.swap, .mul] =
        [.swap, .mul] ++ (List.replicate n ([.swap, .mul] : Code A)).flatten := by
      induction n with
      | zero => rfl
      | succ n hn => simpa [List.replicate_succ, List.append_assoc] using congrArg (fun w => ([.swap, .mul] : Code A) ++ w) hn
    exact commute ds.length

end Holant.OneHot.StackProgram.GraphCodeMachine.Components
