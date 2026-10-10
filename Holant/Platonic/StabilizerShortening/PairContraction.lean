import Holant.Platonic.StabilizerShortening.PhysicalCards
import Holant.Platonic.StabilizerShortening.InverseAxes
import Holant.Platonic.StabilizerShortening.PairGeometry

/-! Exact two-port contraction in the finite axis coordinates. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerErasure Holant.Platonic.StabilizerCode
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {k m n : ℕ}

def coordinateMap (A : Fin n → Kernel ℂ) : Signature ℂ n →ₗ[ℂ] Signature ℂ n where
  toFun := Signature.coordinateAction A
  map_add' := Signature.coordinateAction_add A
  map_smul' c f := by ext x;simp [Signature.coordinateAction,Finset.mul_sum,mul_left_comm]

@[simp] theorem coordinateMap_apply (A : Fin n → Kernel ℂ) (f : Signature ℂ n) :
    coordinateMap A f=Signature.coordinateAction A f := rfl

@[simp] theorem coordinateAction_ket (A : Fin n → Kernel ℂ) (z x : Word n) :
    Signature.coordinateAction A (ket z) x=∏j : Fin n,A j (x j) (z j) := by
  simp [Signature.coordinateAction,ket]

theorem pair_product (p : (Bool ⊕ Fin n) ≃ Fin m) (A : Fin m → Kernel ℂ)
    (z : Word m) (a b : Bool) (x : Word n) :
    (∏j : Fin m,A j (pairInsert p a b x j) (z j))=
      A (p (.inl false)) a (z (p (.inl false)))*
      A (p (.inl true)) b (z (p (.inl true)))*
      ∏j : Fin n,A (p (.inr j)) (x j) (z (p (.inr j))) := by
  rw [←p.prod_comp,Fintype.prod_sum_type]
  simp [mul_comm]

theorem pairCard_coordinate_ket (p : (Bool ⊕ Fin n) ≃ Fin m)
    (A : Fin m → Kernel ℂ) (K : Kernel ℂ) (z : Word m) :
    pairCard p K (Signature.coordinateAction A (ket z))=
      (Kernel.mul (fun a b=>A (p (.inl false)) b a)
        (Kernel.mul K (A (p (.inl true)))))
          (z (p (.inl false))) (z (p (.inl true))) •
        Signature.coordinateAction (fun j=>A (p (.inr j)))
          (ket (fun j=>z (p (.inr j)))) := by
  ext x
  simp only [pairCard,LinearMap.coe_mk,AddHom.coe_mk,coordinateAction_ket,
    pair_product,Pi.smul_apply,smul_eq_mul,Kernel.mul_apply]
  simp only [Fintype.sum_bool]
  ring

theorem axis_pairCard_inverse_ket (p : (Bool ⊕ Fin n) ≃ Fin m)
    (a : Fin m → Fin 4) (z : Word m) :
    Signature.coordinateAction (fun j=>axisMatrix (a (p (.inr j))))
      (pairCard p (selectedKernel (a (p (.inl false))) (a (p (.inl true))))
        (Signature.coordinateAction (fun j=>inverseAxis (a j)) (ket z)))=
      effectiveKernel (a (p (.inl false))) (a (p (.inl true)))
        (z (p (.inl false))) (z (p (.inl true))) •
        ket (fun j=>z (p (.inr j))) := by
  rw [pairCard_coordinate_ket]
  change coordinateMap _ (_ • _)=_
  rw [map_smul]
  change _ • Signature.coordinateAction _ (Signature.coordinateAction _ _) = _
  rw [axis_inverse_coordinate_cancel]
  rfl

end
end Holant.Platonic.StabilizerShortening
