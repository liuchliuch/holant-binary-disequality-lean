import Holant.Certificates.OctahedralSeparator.MatrixSemantics
import Holant.BoundaryAction
import Holant.TwoPorts

/-! Faithful embedding of actual ordered tensor operations into complex values. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant
noncomputable section

def complexTensor {n : ℕ} (f : Signature Scalar n) : Signature ℂ n := fun x => embed (f x)

theorem complexTensor_injective {n : ℕ} : Function.Injective (complexTensor (n := n)) := by
  intro f g h
  funext x
  exact embed_injective (congrFun h x)

theorem complexTensor_action {n : ℕ} (L : Fin n → Mat) (f : Signature Scalar n) :
    complexTensor (Signature.coordinateAction L f)=
      Signature.coordinateAction (fun j => complexMatrix (L j)) (complexTensor f) := by
  funext x
  change embedding (∑ y, (∏ j, L j (x j) (y j))*f y) = _
  simp only [map_sum,map_mul,map_prod]
  rfl

theorem complexTensor_contract {n : ℕ} (K : Mat) (f : Signature Scalar (n+2)) :
    complexTensor (Signature.contract K f)=
      Signature.contract (complexMatrix K) (complexTensor f) := by
  funext x
  change embedding (∑ a, ∑ b, K a b*f (Fin.cons a (Fin.cons b x))) = _
  simp only [map_sum,map_mul]
  rfl

theorem complexTensor_reindex {n : ℕ} (e : Equiv.Perm (Fin n)) (f : Signature Scalar n) :
    complexTensor (Tensor.reindex e f)=Tensor.reindex e (complexTensor f) := rfl

theorem complexTensor_scale {n : ℕ} (c : Scalar) (f : Signature Scalar n) :
    complexTensor (fun x => c*f x)=embed c • complexTensor f := by
  funext x
  exact embed_mul c (f x)

end
end Holant.Certificates.OctahedralSeparator
