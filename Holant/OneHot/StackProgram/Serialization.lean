import Holant.OneHot.StackProgram.Bounds
import Holant.Complexity.FramedEncoding
import Mathlib.Tactic.FinCases

/-!
# Boolean code/stack serialization and a checked interpreter interface

A three-bit opcode tag is followed by either a coefficient-label encoding or a
three-bit bounded stack index. Framing makes opcode lists self-delimiting. The
interpreter decodes actual code and stack words and rejects decoding errors and
stack underflow. It uses semiring operations as primitives; this is not a TM2
implementation or a polynomial-time machine theorem.
-/

namespace Holant.OneHot.StackProgram

open Computability Holant.Complexity

variable {A K : Type}

deriving instance Fintype for Op

/-- Exactly three bits for the compiler's fixed eight-cell stack window. -/
def indexEncode (i : Fin 8) : List Bool :=
  match i.val with
  | 0 => [false, false, false]
  | 1 => [false, false, true]
  | 2 => [false, true, false]
  | 3 => [false, true, true]
  | 4 => [true, false, false]
  | 5 => [true, false, true]
  | 6 => [true, true, false]
  | _ => [true, true, true]

def indexDecode : List Bool → Option (Fin 8)
  | [false, false, false] => some 0
  | [false, false, true] => some 1
  | [false, true, false] => some 2
  | [false, true, true] => some 3
  | [true, false, false] => some 4
  | [true, false, true] => some 5
  | [true, true, false] => some 6
  | [true, true, true] => some 7
  | _ => none

@[simp] theorem indexDecode_encode (i : Fin 8) : indexDecode (indexEncode i) = some i := by
  fin_cases i <;> rfl

@[simp] theorem indexEncode_length (i : Fin 8) : (indexEncode i).length = 3 := by
  fin_cases i <;> rfl

/-- Instruction serialization is independent of the coefficient interpretation. -/
def opEncode (e : Encoding A Bool) : Op A → List Bool
  | .literal a => false :: false :: false :: e.encode a
  | .zero => [false, false, true]
  | .one => [false, true, false]
  | .copy i => false :: true :: true :: indexEncode i
  | .erase i => true :: false :: false :: indexEncode i
  | .swap => [true, false, true]
  | .add => [true, true, false]
  | .mul => [true, true, true]

def opDecode (e : Encoding A Bool) : List Bool → Option (Op A)
  | false :: false :: false :: bits => (e.decode bits).map .literal
  | [false, false, true] => some .zero
  | [false, true, false] => some .one
  | false :: true :: true :: bits => (indexDecode bits).map .copy
  | true :: false :: false :: bits => (indexDecode bits).map .erase
  | [true, false, true] => some .swap
  | [true, true, false] => some .add
  | [true, true, true] => some .mul
  | _ => none

@[simp] theorem opDecode_encode (e : Encoding A Bool) (op : Op A) :
    opDecode e (opEncode e op) = some op := by
  cases op <;> simp [opEncode, opDecode]

def opEncoding (e : Encoding A Bool) : Encoding (Op A) Bool where
  encode := opEncode e
  decode := opDecode e
  decode_encode := opDecode_encode e

/-- Program terminators and per-instruction frames are actual serialized bits. -/
def codeEncoding (e : Encoding A Bool) : Encoding (Code A) Bool :=
  framedListEncoding (opEncoding e)

def stackEncoding (e : Encoding K Bool) : Encoding (List K) Bool := framedListEncoding e

/-- A concrete fixed-family label encoding, including the empty family. -/
def labelEncoding (n : ℕ) : Encoding (Fin n) Bool where
  encode i := List.replicate i.val true
  decode bits := if h : bits.length < n then some ⟨bits.length, h⟩ else none
  decode_encode i := by simp [i.isLt]

/-- With a fixed coefficient alphabet, each instruction has constant bit length. -/
theorem opEncode_length_le (e : Encoding A Bool) (C : ℕ)
    (h : ∀ a, (e.encode a).length ≤ C) (op : Op A) :
    (opEncode e op).length ≤ C + 6 := by
  cases op <;> simp only [opEncode, List.length_cons, List.length_nil, indexEncode_length]
  · rename_i a
    have := h a
    omega
  all_goals omega

/-- Explicit linear bit length of any finite program under bounded label coding. -/
theorem codeEncoding_length_le (e : Encoding A Bool) (C : ℕ)
    (h : ∀ a, (e.encode a).length ≤ C) (code : Code A) :
    ((codeEncoding e).encode code).length ≤ (2 * C + 14) * code.length + 1 := by
  induction code with
  | nil => simp [codeEncoding, framedListEncoding, framedListEncode]
  | cons op code ih =>
    have hop := opEncode_length_le e C h op
    change (true :: (Holant.Algebraic.frame (opEncode e op) ++
      (codeEncoding e).encode code)).length ≤ _
    simp only [List.length_cons, List.length_append, Holant.Algebraic.frame_length,
      List.length_cons] at *
    simp only [Nat.mul_add, Nat.mul_one]
    omega

/-- The actual compiled closed program is a linear-length Boolean word. -/
theorem compileClosed_bits_length_le (e : Encoding A Bool) (C : ℕ)
    (h : ∀ a, (e.encode a).length ≤ C) (a : A) (ts : Forest A) :
    ((codeEncoding e).encode (compileClosed a ts)).length ≤
      (2 * C + 14) * (13 * ts.vertices + 19 * ts.edges + 5) + 1 := by
  simpa using codeEncoding_length_le e C h (compileClosed a ts)

/-- A finite family of `n` labels gives an explicit constant in the bit bound. -/
theorem compileClosed_finite_bits_length_le {n : ℕ} (a : Fin n) (ts : Forest (Fin n)) :
    ((codeEncoding (labelEncoding n)).encode (compileClosed a ts)).length ≤
      (2 * n + 14) * (13 * ts.vertices + 19 * ts.edges + 5) + 1 := by
  apply compileClosed_bits_length_le
  intro i
  simp [labelEncoding]

variable [CommSemiring K]

/-- Decode code and stack, execute actual instructions, then serialize both the
final stack and the full arithmetic trace. Every failure is represented by `none`. -/
def runBits (labels : Encoding A Bool) (values : Encoding K Bool) (coeff : A → K)
    (code stack : List Bool) : Option (List Bool × List Bool) := do
  let p ← (codeEncoding labels).decode code
  let s ← (stackEncoding values).decode stack
  let (s', trace) ← run coeff p s
  pure ((stackEncoding values).encode s', (stackEncoding values).encode trace)

/-- Interpreter correctness for every well-encoded program, including underflow. -/
theorem runBits_encode (labels : Encoding A Bool) (values : Encoding K Bool)
    (coeff : A → K) (p : Code A) (s : List K) :
    runBits labels values coeff ((codeEncoding labels).encode p)
      ((stackEncoding values).encode s) =
      (run coeff p s).map (fun r => ((stackEncoding values).encode r.1,
        (stackEncoding values).encode r.2)) := by
  simp [runBits, Option.map_eq_bind]

/-- Serialized closed evaluation preserves the exact arithmetic trace. -/
theorem runBits_compileClosed (labels : Encoding A Bool) (values : Encoding K Bool)
    (coeff : A → K) (a : A) (ts : Forest A) (s : List K) :
    runBits labels values coeff ((codeEncoding labels).encode (compileClosed a ts))
      ((stackEncoding values).encode s) =
      some ((stackEncoding values).encode
        (((interpretForest coeff ts).closedProgram (coeff a)).run.1 :: s),
        (stackEncoding values).encode
          ((interpretForest coeff ts).closedProgram (coeff a)).values) := by
  simp [runBits_encode, run_compileClosed]

end Holant.OneHot.StackProgram
