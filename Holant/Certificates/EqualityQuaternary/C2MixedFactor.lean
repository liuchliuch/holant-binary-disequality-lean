import Holant.Certificates.EqualityQuaternary.C2MixedWalsh

/-! The exceptional y=0,x²+z²=0 mixed table has a genuine 13|24
factorization. Inverse Walsh action carries those actual factors back to
the original physical tensor, so source primality rules this case out.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2.Mixed
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicQuaternary
open Holant.Projective.CyclicQuaternary.Physical hiding Scalar Mat
open Holant.ReedMuller.CoefficientAtlas
set_option backward.isDefEq.respectTransparency false

def crossingPorts : (Fin 2 ⊕ Fin 2) ≃ Fin 4 where
  toFun := Sum.elim (fun i => if i=0 then 0 else 2) (fun i => if i=0 then 1 else 3)
  invFun := ![.inl 0,.inr 0,.inl 1,.inr 1]
  left_inv := by rintro (i|i) <;> fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def leftFactor (x z : Scalar) : Signature Scalar 2 := fun w =>
  if w 0 then (if w 1 then 0 else z) else (if w 1 then x else 0)
def rightFactor (x z : Scalar) : Signature Scalar 2 := fun w =>
  if w 0 then (if w 1 then 0 else -z/x) else (if w 1 then 1 else 0)

theorem mixed_factor (x z : Scalar) (hx : x≠0) (hdet : x^2+z^2=0) :
    mixedTable x 0 z=Tensor.reindex crossingPorts (Tensor.tensor (leftFactor x z) (rightFactor x z)) := by
  funext w
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [mixedTable,ofCoordinates,Tensor.reindex,Tensor.tensor,crossingPorts,
      leftFactor,rightFactor,Equiv.swap_apply_def,h0,h1,h2,h3,hx]
  · field_simp [hx]
  · have hr : -(z*z)/x=x := (div_eq_iff hx).mpr (by linear_combination -hdet)
    calc
      x = -(z*z)/x := hr.symm
      _ = z*(-z/x) := by ring

theorem binary_factor_action (M : Mat) (p : (Fin 2 ⊕ Fin 2) ≃ Fin 4)
    (f g : Signature Scalar 2) :
    Signature.coordinateAction (fun _ => M) (Tensor.reindex p (Tensor.tensor f g)) =
      Tensor.reindex p (Tensor.tensor (Signature.coordinateAction (fun _ => M) f)
        (Signature.coordinateAction (fun _ => M) g)) := by
  let e : Equiv.Perm (Fin 4) := finSumFinEquiv.symm.trans p
  have hs (f g : Signature Scalar 2) : Tensor.reindex p (Tensor.tensor f g)=
      Tensor.reindex e (Signature.tensor f g) := by
    funext w
    simp [e,Signature.tensor,Tensor.reindex,Tensor.tensor]
  rw [hs,coordinateAction_reindex,
    EightVertex.ProductAnchor.coordinateAction_tensor (m:=2) (n:=2),←hs]

theorem physical_mixed_factor (q : Signature Scalar 4) (x z : Scalar)
    (hx : x≠0) (hdet : x^2+z^2=0) (h : walsh q=mixedTable x 0 z) : ProperFactor q := by
  have hinv : Signature.coordinateAction (fun _ => P) (walsh q)=q :=
    Signature.coordinateAction_cancel _ _ (fun _ => P_Pinv) q
  rw [h,mixed_factor x z hx hdet,binary_factor_action] at hinv
  exact ⟨2,2,by decide,by decide,crossingPorts,_,_,hinv.symm⟩

theorem prime_mixed_nonzero_sum (q : Signature Scalar 4) (x z : Scalar)
    (hp : TensorPrime q) (hx : x≠0) (h : walsh q=mixedTable x 0 z) : x^2+z^2≠0 :=
  fun hz => hp.2 (physical_mixed_factor q x z hx hz h)

end Holant.Certificates.EqualityQuaternary.C2.Mixed
