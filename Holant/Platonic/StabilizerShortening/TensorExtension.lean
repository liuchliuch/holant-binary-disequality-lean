import Holant.Platonic.StabilizerErasure.TensorAuxiliary

/-! Identity on an arbitrary number of untouched ports, with literal ordered
Boolean slices. Arithmetic is k+t; the t untouched ports are first. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable.AffinePhase
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
open Holant.Platonic.StabilizerErasure
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {k n m : ℕ}

def tensorMap (t : ℕ) (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    Signature ℂ (k+t) →ₗ[ℂ] Signature ℂ (n+t) :=
  match t with
  | 0 => U
  | t+1 => prependMap (tensorMap t U)

@[simp] theorem tensorMap_zero (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    tensorMap 0 U=U := rfl

@[simp] theorem tensorMap_succ (t : ℕ) (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    tensorMap (t+1) U=prependMap (tensorMap t U) := rfl

theorem prependMap_comp (V : Signature ℂ n →ₗ[ℂ] Signature ℂ m)
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    prependMap (V.comp U)=(prependMap V).comp (prependMap U) := by
  apply LinearMap.ext
  intro f
  ext w
  change V (U (column 0 (w 0) f)) (Fin.tail w)=
    V (column 0 (w 0) (prependMap U f)) (Fin.tail w)
  rw [column_prependMap]

theorem tensorMap_comp (t : ℕ) (V : Signature ℂ n →ₗ[ℂ] Signature ℂ m)
    (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n) :
    tensorMap t (V.comp U)=(tensorMap t V).comp (tensorMap t U) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [tensorMap_succ,ih,prependMap_comp];rfl

@[simp] theorem prependMap_id :
    prependMap (LinearMap.id : Signature ℂ k →ₗ[ℂ] Signature ℂ k)=LinearMap.id := by
  ext f w
  simp [prependMap,column,Fin.insertNth_zero]

@[simp] theorem tensorMap_id (t : ℕ) :
    tensorMap t (LinearMap.id : Signature ℂ k →ₗ[ℂ] Signature ℂ k)=LinearMap.id := by
  induction t with
  | zero => rfl
  | succ t ih => rw [tensorMap_succ,ih,prependMap_id]

theorem tensorMap_stabilizer (t : ℕ) (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (hU : IsStabilizerIsometry U) : IsStabilizerIsometry (tensorMap t U) := by
  induction t with
  | zero => exact hU
  | succ t ih => exact prependMap_stabilizer _ ih

/-- A literal assignment consisting of t untouched bits followed by k bits. -/
def wordTensor : (t : ℕ) → Word t → Word k → Word (k+t)
  | 0,_,z => z
  | t+1,x,z => Fin.cons (x 0) (wordTensor t (Fin.tail x) z)

@[simp] theorem wordTensor_zero (x : Word 0) (z : Word k) : wordTensor 0 x z=z := rfl
@[simp] theorem wordTensor_succ (t : ℕ) (x : Word (t+1)) (z : Word k) :
    wordTensor (t+1) x z=Fin.cons (x 0) (wordTensor t (Fin.tail x) z) := rfl

/-- The extension is exactly I^t tensor U, on the actual ordered coordinates. -/
theorem tensorMap_wordTensor (t : ℕ) (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (f : Signature ℂ (k+t)) (x : Word t) (y : Word n) :
    tensorMap t U f (wordTensor t x y)=U (fun z=>f (wordTensor t x z)) y := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change tensorMap t U (column 0 (x 0) f) (wordTensor t (Fin.tail x) y)=
      U (fun z=>f (Fin.cons (x 0) (wordTensor t (Fin.tail x) z))) y
    rw [ih]
    simp only [column_zero_apply]

end
end Holant.Platonic.StabilizerShortening
