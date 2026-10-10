import Holant.Certificates.AffineEndpoint.WordCode
import Holant.Tractable.AffineOperations
import Mathlib.Data.List.Sublists

/-! Computable binary affine maps used by the literal quaternary charts. -/
namespace Holant.Certificates.AffineEndpoint.SupportCatalog
open Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def binaryBool (a : ZMod 2) : Bool := decide (a = 1)

@[simp] theorem bitValue_binaryBool (a : ZMod 2) : bitValue (ZMod 2) (binaryBool a) = a := by
  rcases binary_cases a with rfl | rfl <;> decide

def matrixWord {m n : ℕ} (A : Fin n → Fin m → ZMod 2) (x : Word m) : Word n :=
  fun i => binaryBool (rowDot (A i) x)

theorem matrixWord_xor {m n : ℕ} (A : Fin n → Fin m → ZMod 2) (x y : Word m) :
    matrixWord A (xor x y) = xor (matrixWord A x) (matrixWord A y) := by
  funext i
  apply bitValue_injective
  simp [matrixWord, xor_apply]

@[simp] theorem matrixWord_origin {m n : ℕ} (A : Fin n → Fin m → ZMod 2) :
    matrixWord A (origin m) = origin n := by
  funext i
  simp [matrixWord, binaryBool, origin]

theorem translated_matrixWord_affine {m n : ℕ} (A : Fin n → Fin m → ZMod 2)
    (a : Word n) : IsAffineMap (fun x => xor a (matrixWord A x)) := by
  intro x y
  dsimp only
  rw [matrixWord_xor, matrixWord_origin]
  funext i
  simp only [xor_apply, origin]
  cases a i <;> cases matrixWord A x i <;> cases matrixWord A y i <;> rfl

theorem matrixWord_translate_affine {m n : ℕ} (A : Fin n → Fin m → ZMod 2)
    (a : Word m) : IsAffineMap (fun x => matrixWord A (xor a x)) := by
  have he : (fun x => matrixWord A (xor a x)) =
      (fun x => xor (matrixWord A a) (matrixWord A x)) := by
    funext x
    exact matrixWord_xor A a x
  rw [he]
  exact translated_matrixWord_affine A (matrixWord A a)

def codeXor (a b : Fin 16) : Fin 16 := ⟨(a.val ^^^ b.val) % 16, Nat.mod_lt _ (by decide)⟩

theorem codeWord_codeXor : ∀ a b, codeWord (codeXor a b) = xor (codeWord a) (codeWord b) := by
  decide +kernel

/-- The verifier's iterative XOR span, on its literal integer word codes. -/
def codeSpan : List (Fin 16) → Finset (Fin 16)
  | [] => {0}
  | a :: as => codeSpan as ∪ (codeSpan as).image (codeXor a)

/-- The verifier chooses the first increasing nonzero combination of the
prescribed dimension which spans the space. `sublistsLen` has reverse
combination order, hence the explicit reversal. -/
def sourceCanonicalBasis (S : Finset (Fin 16)) (d : ℕ) : List (Fin 16) :=
  ((((List.finRange 16).filter (fun a => decide (a ∈ S ∧ a ≠ 0))).sublistsLen d).reverse.find?
    (fun b => decide (codeSpan b = S))).getD []

theorem mem_translateSet_iff {n : ℕ} (a x : Word n) (S : Finset (Word n)) :
    x ∈ translateSet a S ↔ xor a x ∈ S := by
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨xor a x, hx, xor_cancel_left a x⟩

end Holant.Certificates.AffineEndpoint.SupportCatalog
