import Holant.Certificates.OctahedralSeparator.SourceTransport
import Holant.Certificates.OctahedralSeparator.TensorSemantics
import Holant.Certificates.OctahedralSeparator.GroupRepresentatives

namespace Holant.Certificates.OctahedralSeparator
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

theorem quaternion_dual : ∀ μ ν : Fin 4,
    (∑ a : Bool, ∑ b : Bool, q μ a b*dual ν a b) = if ν=μ then 1 else 0 := by decide +kernel

theorem quaternion_card_reconstruct (μ : Fin 4) (F : Fin 4 → Signature Scalar 4) :
    Signature.contract (q μ) (reconstruct F)=F μ := by
  rw [contract_reconstruct]
  funext x
  simp only [quaternion_dual]
  simp

theorem transported_basis_card (f : Form) (μ : Fin 4) (F : Fin 4 → Signature Scalar 4) :
    Signature.contract (theta f (q μ)) (Signature.coordinateAction (sixLegs f) (reconstruct F))=
      Signature.coordinateAction (coefficientLegs f) (F μ) := by
  rw [contract_action]
  change Signature.coordinateAction (coefficientLegs f)
      (Signature.contract (pairKernel (mt (conjugator f)) (inverseConjugator f)
        (theta f (q μ))) (reconstruct F)) = _
  rw [pairKernel_theta,quaternion_card_reconstruct]

/-- The source's normalized actual card-map dictionary, in the fixed physical
coordinates. It specifies contractions, without assuming an output or gadget. -/
def NormalizedCardMap (f : Form) (F : Fin 4 → Signature Scalar 4) (h : Signature ℂ 6) : Prop :=
  ∀ μ : Fin 4, Signature.contract (complexMatrix (theta f (q μ))) h =
    complexTensor (Signature.coordinateAction (coefficientLegs f) (F μ))

theorem reconstructed_normalized (f : Form) (F : Fin 4 → Signature Scalar 4) :
    NormalizedCardMap f F
      (complexTensor (Signature.coordinateAction (sixLegs f) (reconstruct F))) := by
  intro μ
  rw [← complexTensor_contract,transported_basis_card]

theorem contract_kernel_add (U V : Kernel ℂ) (h : Signature ℂ 6) :
    Signature.contract (U+V) h=Signature.contract U h+Signature.contract V h := by
  funext x
  simp [Signature.contract,add_mul,Finset.sum_add_distrib]

theorem theta_add (f : Form) (U V : Mat) : theta f (U+V)=theta f U+theta f V := by
  funext a b
  simp only [theta,mm,Pi.add_apply]
  ring

theorem normalized_first_card (f : Form) (frame : Fin 4) (order : Fin 6)
    (h : Signature ℂ 6) (hN : NormalizedCardMap f (fullImages frame order) h) :
    Signature.contract (complexMatrix (theta f firstKernel)) h=
      complexTensor (coefficientCard f (Fin.castAdd 6 (frames frame (permutations order 0)))) := by
  unfold firstKernel
  rw [theta_add,complexMatrix_add,contract_kernel_add,hN 0,hN 1]
  funext x
  change embed (Signature.coordinateAction (coefficientLegs f) (fullImages frame order 0) x)+
    embed (Signature.coordinateAction (coefficientLegs f) (fullImages frame order 1) x)=_
  rw [← embed_add]
  apply congrArg embed
  change (Signature.coordinateAction (coefficientLegs f) (fullImages frame order 0)+
    Signature.coordinateAction (coefficientLegs f) (fullImages frame order 1)) x=_
  rw [← Signature.coordinateAction_add]
  simp only [coefficientCard,baseCard,Fin.addCases_left]
  rfl

end
end Holant.Certificates.OctahedralSeparator
