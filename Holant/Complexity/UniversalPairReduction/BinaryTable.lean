import Holant.Kernel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact ordered binary reconstruction for source Lemma 3.2. This module is
algebraic only: `close` and `insert` are not asserted to be oracle algorithms. -/
namespace Holant.Complexity.UniversalPairReduction

abbrev BinaryTable (K : Type*) := Bool → Bool → K

namespace BinaryTable
variable {K : Type*}

def transpose (B : BinaryTable K) : BinaryTable K := fun a b => B b a

def complement (B : BinaryTable K) : BinaryTable K := fun a b => B (!a) (!b)

def Symmetric (B : BinaryTable K) : Prop := B false true = B true false

@[simp] theorem transpose_transpose (B : BinaryTable K) : B.transpose.transpose = B := rfl
@[simp] theorem complement_complement (B : BinaryTable K) : B.complement.complement = B := by
  funext a b
  simp [complement]

theorem symmetric_complement_iff (B : BinaryTable K) : B.complement.Symmetric ↔ B.Symmetric := by
  simp only [Symmetric,complement,Bool.not_false,Bool.not_true]
  exact eq_comm

section Semiring
variable [CommSemiring K]

def close (H : BinaryTable K) : K := H false true + H true false

def insert (H B : BinaryTable K) : K :=
  B false false * H false false + B false true * H false true +
    B true false * H true false + B true true * H true true

def delta : BinaryTable K := fun a b => if a = false ∧ b = true then 1 else 0

@[simp] theorem insert_delta (H : BinaryTable K) : H.insert delta = H false true := by
  simp [insert,delta]

@[simp] theorem insert_disequality (H : BinaryTable K) :
    H.insert Signature.disequality = H.close := by
  simp [insert,close,Signature.disequality]

end Semiring
section Field
variable [Field K] [CharZero K]

theorem reconstruct_symmetric (H : BinaryTable K) (h : H.Symmetric) :
    H false true = H.close / 2 := by
  unfold Symmetric at h
  unfold close
  rw [←h]
  field_simp
  <;> ring

theorem ordered_difference (H B : BinaryTable K) :
    H.insert B - H.insert B.transpose =
      (B false true - B true false) * (H false true - H true false) := by
  simp only [insert,transpose]
  ring

theorem reconstruct_asymmetric (H B : BinaryTable K)
    (h : B false true ≠ B true false) :
    H false true = (H.close + (H.insert B - H.insert B.transpose) /
      (B false true - B true false)) / 2 := by
  rw [ordered_difference]
  have hn : B false true - B true false ≠ 0 := sub_ne_zero.mpr h
  unfold close
  field_simp [hn]
  ring

/-- A deleted self-loop contributes a native X table times the value of the
remaining closed components. Its X-closure contributes a genuine factor two. -/
def loopRaw (z : K) : BinaryTable K := fun a b => z * Signature.disequality a b

@[simp] theorem loopRaw_01 (z : K) : loopRaw z false true = z := by
  simp [loopRaw,Signature.disequality]

@[simp] theorem loopRaw_10 (z : K) : loopRaw z true false = z := by
  simp [loopRaw,Signature.disequality]

theorem loopRaw_close (z : K) : (loopRaw z).close = 2*z := by
  simp [close]
  ring

theorem loopRaw_insert (z : K) (B : BinaryTable K) :
    (loopRaw z).insert B = (B false true + B true false)*z := by
  simp [insert,loopRaw,Signature.disequality]
  ring

end Field
end BinaryTable
end Holant.Complexity.UniversalPairReduction
