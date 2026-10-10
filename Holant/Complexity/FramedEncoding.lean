import Holant.Algebraic.RationalEncoding

/-!
# Explicit framed product and list encodings

Even an empty scalar word occupies a delimiter. Every list entry, including a zero
label or empty vertex record, occupies at least two bits. The actual decoders are
fuel-bounded parsers with proved round trips, not just length-witness wrappers.
-/

namespace Holant.Complexity

open Computability Holant.Algebraic

/-- A framed first component followed by the second component's full code. -/
def framedProductEncoding {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool) :
    Encoding (α × β) Bool where
  encode p := frame (ea.encode p.1) ++ eb.encode p.2
  decode bits := do
    let (first, rest) ← unframe bits
    let a ← ea.decode first
    let b ← eb.decode rest
    pure (a, b)
  decode_encode p := by simp

@[simp] theorem framedProductEncoding_length {α β : Type}
    (ea : Encoding α Bool) (eb : Encoding β Bool) (p : α × β) :
    ((framedProductEncoding ea eb).encode p).length =
      2 * (ea.encode p.1).length + 1 + (eb.encode p.2).length := by
  simp [framedProductEncoding]

/-- A list terminator or an entry marker followed by a framed element and tail. -/
def framedListEncode {α : Type} (e : Encoding α Bool) : List α → List Bool
  | [] => [false]
  | a :: rest => true :: (frame (e.encode a) ++ framedListEncode e rest)

/-- Parse a list prefix with a decreasing natural fuel parameter. No unchecked
termination assumption is needed for parsing arbitrary malformed input. -/
def framedListDecodePrefix {α : Type} (e : Encoding α Bool) :
    ℕ → List Bool → Option (List α × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, false :: rest => some ([], rest)
  | fuel + 1, true :: rest => do
    let (head, remaining) ← unframe rest
    let a ← e.decode head
    let (tail, suffix) ← framedListDecodePrefix e fuel remaining
    pure (a :: tail, suffix)

/-- Enough fuel for one parser step per element plus the terminator suffices. -/
theorem framedListDecodePrefix_encode_append {α : Type} (e : Encoding α Bool)
    (xs : List α) (suffix : List Bool) (fuel : ℕ) (h : xs.length + 1 ≤ fuel) :
    framedListDecodePrefix e fuel (framedListEncode e xs ++ suffix) = some (xs, suffix) := by
  induction xs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at h
    | succ fuel => rfl
  | cons a xs ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      have hf : xs.length + 1 ≤ fuel := by simpa using h
      simp [framedListEncode, framedListDecodePrefix, List.append_assoc, ih fuel hf]

/-- Explicit entries cannot disappear, even if their element code is empty. -/
theorem framedListEncode_length_lower {α : Type} (e : Encoding α Bool) (xs : List α) :
    2 * xs.length + 1 ≤ (framedListEncode e xs).length := by
  induction xs with
  | nil => simp [framedListEncode]
  | cons a xs ih =>
    simp only [framedListEncode, List.length_cons, List.length_append, frame_length]
    omega

/-- The complete list decoder rejects a trailing suffix. -/
def framedListEncoding {α : Type} (e : Encoding α Bool) : Encoding (List α) Bool where
  encode := framedListEncode e
  decode bits := (framedListDecodePrefix e bits.length bits).bind
    (fun p => if p.2 = [] then some p.1 else none)
  decode_encode xs := by
    have hlen : xs.length + 1 ≤ (framedListEncode e xs).length := by
      have h := framedListEncode_length_lower e xs
      omega
    have h := framedListDecodePrefix_encode_append e xs [] (framedListEncode e xs).length hlen
    simpa using congrArg (fun x => x.bind (fun p => if p.2 = [] then some p.1 else none)) h

/-- Actual bit length, not a freely chosen size annotation. -/
theorem framedListEncoding_length_lower {α : Type} (e : Encoding α Bool) (xs : List α) :
    2 * xs.length + 1 ≤ ((framedListEncoding e).encode xs).length :=
  framedListEncode_length_lower e xs

end Holant.Complexity
