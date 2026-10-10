import Holant.Complexity.FramedEncoding
import Holant.Complexity.OutputSize
import Mathlib.Tactic.Linarith
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Support.EncodingSize
open Holant.Complexity Computability
 theorem nat_code_length_le (n : ℕ) : (encodingNatBool.encode n).length ≤ n := by
  change (encodeNat n).length ≤ n
  rw [Holant.Algebraic.encodeNat_length]
  exact Nat.size_le.mpr n.lt_two_pow_self

 theorem framedList_length_le {α : Type} (e : Encoding α Bool) (xs : List α) (C : ℕ)
    (h : ∀ x ∈ xs, (e.encode x).length ≤ C) :
    (framedListEncode e xs).length ≤ (2*C+2)*xs.length+1 := by
  induction xs with
  | nil => simp [framedListEncode]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simp only [framedListEncode, List.length_cons, List.length_append,
      Holant.Algebraic.frame_length]
    nlinarith


end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Support.EncodingSize
