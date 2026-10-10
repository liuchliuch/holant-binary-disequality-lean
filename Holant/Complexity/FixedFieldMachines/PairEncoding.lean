import Holant.Algebraic.RationalEncoding
import Holant.Complexity.BinaryCompose.Identity

/-! An explicit product wire protocol. Only the first component is framed; the
second occupies the remaining suffix. In particular a scalar followed by a
vector is exactly the existing vector codec, with no codec replacement. -/
namespace Holant.Complexity.FixedFieldMachines
open Computability BinaryCompose

def pairEncoding {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool) :
    Encoding (α × β) Bool where
  encode p := Holant.Algebraic.frame (ea.encode p.1) ++ eb.encode p.2
  decode word := do
    let (first, rest) ← Holant.Algebraic.unframe word
    let a ← ea.decode first
    let b ← eb.decode rest
    pure (a, b)
  decode_encode p := by simp [Holant.Algebraic.unframe_frame_append, ea.decode_encode, eb.decode_encode]

@[simp] theorem pairEncoding_encode {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool)
    (p : α × β) : (pairEncoding ea eb).encode p =
      Holant.Algebraic.frame (ea.encode p.1) ++ eb.encode p.2 := rfl

@[simp] theorem pairEncoding_length {α β : Type} (ea : Encoding α Bool) (eb : Encoding β Bool)
    (p : α × β) : ((pairEncoding ea eb).encode p).length =
      2 * (ea.encode p.1).length + 1 + (eb.encode p.2).length := by
  simp [pairEncoding]

/-- Change only the specification types when the actual input and output words
are literally equal. The finite program and its time polynomial are retained. -/
def recode {α β γ δ : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {ec : Encoding γ Bool} {ed : Encoding δ Bool} {f : α → β} {g : γ → δ}
    (w : Computes ea eb f) (input : γ → α)
    (hi : ∀ x, ea.encode (input x) = ec.encode x)
    (ho : ∀ x, eb.encode (f (input x)) = ed.encode (g x)) : Computes ec ed g where
  machine := w.machine
  time := w.time
  outputs x := by
    have h := w.outputs (input x)
    rw [hi, ho] at h
    exact h

/-- Extensional replacement never modifies a program. -/
def congrComputes {α β : Type} {ea : Encoding α Bool} {eb : Encoding β Bool}
    {f g : α → β} (w : Computes ea eb f) (h : ∀ x, f x = g x) : Computes ea eb g :=
  recode w id (fun _ => rfl) (fun x => congrArg eb.encode (h x))

end Holant.Complexity.FixedFieldMachines
