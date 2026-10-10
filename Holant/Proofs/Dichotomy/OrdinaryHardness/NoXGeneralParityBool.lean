import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralRankTwoParity
import Mathlib.Data.Nat.Bits

/-! Boolean certificates are connected to the literal natural-number port
counts through exact parity identities, not by replacing those counts. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralParityBool
set_option maxHeartbeats 500000
set_option Elab.async false

theorem even_iff (n : ℕ) : Even n ↔ Nat.bodd n=false := by
  rw [Nat.even_iff,Nat.mod_two_of_bodd]
  cases Nat.bodd n <;> decide

theorem odd_iff (n : ℕ) : Odd n ↔ Nat.bodd n=true := by
  rw [Nat.odd_iff,Nat.mod_two_of_bodd]
  cases Nat.bodd n <;> decide

theorem conditional (b : Bool) (n : ℕ) : Nat.bodd (if b then n else 0)=(b && Nat.bodd n) := by
  cases b <;> simp

theorem cancel (a b c : Bool) (h : a=(b ^^ c)) : ((a ^^ b) ^^ c)=false := by
  rw [h]
  cases b <;> cases c <;> rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralParityBool
