import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinH6RMBell
import Mathlib.Data.Fintype.Prod
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixFiniteForms

/-! The literal H6 parity block is a four-point Walsh transform with linear
input signs. An even-phase input face has a zero and a nonzero output. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineWalsh
open Holant Holant.Tractable Holant.Algebraic
open scoped BigOperators
namespace H
export GlobalCloseCompletionKleinH6RMBell (core)
end H
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def triple (d a b : Bool) : Fin 3→Bool := ![a,b,d^^a^^b]
def six (d a b u v : Bool) : Fin 6→Bool := ![a,b,d^^a^^b,u,v,d^^u^^v]
def sign {K : Type*} [Ring K] (b : Bool) : K := if b then -1 else 1

def output {K : Type*} [Field K] (d : Bool) (s : Bool→Bool→Bool) (a b : Bool) : K :=
  ∑u : Bool,∑v : Bool,H.core (six d a b u v)*sign (s u v)

/-- This finite certificate keeps the original physical six-port order. -/
theorem integer_witness (d : Bool) (s : Bool→Bool→Bool)
    (even : sign (K:=ℚ) (s false false)*sign (s true true)=
      sign (s false true)*sign (s true false)) :
    ∃a b a' b',output (K:=ℚ) d s a b=0 ∧
      (output (K:=ℚ) d s a' b'=4 ∨ output (K:=ℚ) d s a' b'= -4) := by
  revert d s
  decide +kernel

variable {K : Type*} [Field K] [CharZero K]

theorem output_cast (d : Bool) (s : Bool→Bool→Bool) (a b : Bool) :
    output (K:=K) d s a b=(output (K:=ℚ) d s a b:K) := by
  simp only [output,← GlobalCloseCompletionKleinSixFiniteForms.core_cast,
    Rat.cast_sum,Rat.cast_mul,Rat.cast_intCast]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  cases s u v <;> simp [sign]

theorem witness (d : Bool) (s : Bool→Bool→Bool)
    (even : sign (K:=K) (s false false)*sign (s true true)=
      sign (s false true)*sign (s true false)) :
    ∃a b a' b',output (K:=K) d s a b=0 ∧ output (K:=K) d s a' b'≠0 := by
  have evenQ : sign (K:=ℚ) (s false false)*sign (s true true)=
      sign (s false true)*sign (s true false) := by
    have cast : ∀b,(sign (K:=ℚ) b:K)=sign (K:=K) b := by intro b;cases b <;> simp [sign]
    apply Rat.cast_injective (α:=K)
    simpa only [Rat.cast_mul,cast] using even
  obtain ⟨a,b,a',b',zero,live⟩ := integer_witness d s evenQ
  refine ⟨a,b,a',b',?_,?_⟩
  · rw [output_cast,zero,Rat.cast_zero]
  · rw [output_cast]
    rcases live with live|live <;> rw [live] <;> norm_num

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineWalsh
end
