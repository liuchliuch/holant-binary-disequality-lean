import Holant.Proofs.CountingMachines.StandardMachine.Support.Foundation

set_option backward.isDefEq.respectTransparency false
/-! Adapted reference proof. See the task validation reports. Fixed two-bit canonical edge packets.
00 is the deterministic edge, 10/11 are the two split edges, 01 is invalid.
EOF in either position is invalid; it is never a guessed padding bit.
-/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Packet

def first : Option Bool → Bool
  | none => false
  | some _ => true

def second : Option Bool → Bool
  | none => false
  | some b => b

def encode (token : Option Bool) : List Bool := [first token,second token]

def decode : Option Bool → Option Bool → Option (Option Bool)
  | some false,some false => some none
  | some true,some b => some (some b)
  | _,_ => none

@[simp] theorem encode_length (token : Option Bool) : (encode token).length = 2 := rfl

@[simp] theorem decode_encode (token : Option Bool) :
    decode (some (first token)) (some (second token)) = some token := by
  cases token with
  | none => rfl
  | some b => cases b <;> rfl

theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh : first a = first b ∧ second a = second b := by
    simpa [encode] using h
  have hd := congrArg₂ decode (congrArg some hh.1) (congrArg some hh.2)
  simpa only [decode_encode,Option.some.injEq] using hd

@[simp] theorem malformed : decode (some false) (some true) = none := rfl
@[simp] theorem first_eof (b : Option Bool) : decode none b = none := rfl
@[simp] theorem second_eof (b : Option Bool) : decode b none = none := by
  cases b with
  | none => rfl
  | some a => cases a <;> rfl

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.Packet
