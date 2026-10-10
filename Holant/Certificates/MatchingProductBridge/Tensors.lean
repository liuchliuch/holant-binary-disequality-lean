import Holant.Signature
import Holant.Tensor
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-! Literal ordered matching tensors and quaternion constants from Lemma A.15.
These are exact complex identities, with ordinary transpose and no conjugation. -/
namespace Holant.Certificates.MatchingProductBridge
open Holant
abbrev Binary := Bool → Bool → ℂ
abbrev FourTensor := Signature ℂ 4

def P0 (U V : Binary) : FourTensor := fun x => U (x 0) (x 1) * V (x 2) (x 3)
def P1 (U V : Binary) : FourTensor := fun x => U (x 0) (x 2) * V (x 1) (x 3)
def P2 (U V : Binary) : FourTensor := fun x => U (x 0) (x 3) * V (x 1) (x 2)

def Q0 : Binary := Signature.equality
def Q1 : Binary := fun a b => if a = b then 0 else Complex.I
def Q2 : Binary := fun a b => if a = b then 0 else if a then -1 else 1
def Q3 : Binary := fun a b => if a = b then if a then -Complex.I else Complex.I else 0

def A : FourTensor := P0 Q0 Q0
def B : FourTensor := P1 Q0 Q0
def C : FourTensor := P2 Q2 Q2

theorem A_sub_B : A - B = C := by
  funext x
  rcases hx : x 0 with _ | _ <;> rcases hy : x 1 with _ | _ <;>
    rcases hz : x 2 with _ | _ <;> rcases hw : x 3 with _ | _ <;>
    simp [A,B,C,P0,P1,P2,Q0,Q2,Signature.equality,hx,hy,hz,hw]

theorem A_add_B : A + B = P2 Q0 Q0 - P2 Q1 Q1 - P2 Q3 Q3 := by
  funext x
  rcases hx : x 0 with _ | _ <;> rcases hy : x 1 with _ | _ <;>
    rcases hz : x 2 with _ | _ <;> rcases hw : x 3 with _ | _ <;>
    simp [A,B,P0,P1,P2,Q0,Q1,Q3,Signature.equality,hx,hy,hz,hw,Complex.I_sq]

def symmetricQuaternion (u : Fin 3 → ℝ) : Binary :=
  fun a b => (u 0 : ℂ)*Q0 a b + (u 1 : ℂ)*Q1 a b + (u 2 : ℂ)*Q3 a b

def conjugateQuaternion (u : Fin 3 → ℝ) : Binary :=
  fun a b => (u 0 : ℂ)*Q0 a b - (u 1 : ℂ)*Q1 a b - (u 2 : ℂ)*Q3 a b

def normSquare (u : Fin 3 → ℝ) : ℝ := (u 0)^2+(u 1)^2+(u 2)^2

def multiply (U V : Binary) : Binary := fun a b => U a false * V false b + U a true * V true b

def transpose (U : Binary) : Binary := fun a b => U b a

theorem symmetricQuaternion_transpose (u : Fin 3 → ℝ) : transpose (symmetricQuaternion u) = symmetricQuaternion u := by
  funext a b
  cases a <;> cases b <;> simp [transpose,symmetricQuaternion,Q0,Q1,Q3,Signature.equality]

theorem quaternion_mul_conjugate (u : Fin 3 → ℝ) :
    multiply (symmetricQuaternion u) (conjugateQuaternion u) =
      fun a b => (normSquare u : ℂ)*Q0 a b := by
  funext a b
  cases a <;> cases b <;>
    simp [multiply,symmetricQuaternion,conjugateQuaternion,normSquare,Q0,Q1,Q3,
      Signature.equality,Complex.ofReal_add,Complex.ofReal_pow] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem conjugate_mul_quaternion (u : Fin 3 → ℝ) :
    multiply (conjugateQuaternion u) (symmetricQuaternion u) =
      fun a b => (normSquare u : ℂ)*Q0 a b := by
  funext a b
  cases a <;> cases b <;>
    simp [multiply,symmetricQuaternion,conjugateQuaternion,normSquare,Q0,Q1,Q3,
      Signature.equality,Complex.ofReal_add,Complex.ofReal_pow] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

end Holant.Certificates.MatchingProductBridge
