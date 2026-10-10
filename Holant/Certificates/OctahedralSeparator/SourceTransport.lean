import Holant.Certificates.OctahedralSeparator.TensorData
import Holant.Certificates.OctahedralSeparator.TensorTransport
import Holant.Certificates.OctahedralSeparator.MatrixSemantics

/-! The actual first-pair cards and the original 1/3 deficient cards. All
similarities in this module are coefficient identities, not gadget resources. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem kernel_mul_eq_mm (U V : Mat) : Kernel.mul U V=mm U V := by
  funext a b
  simp [Kernel.mul,mm,add_comm]

theorem firstKernel_dual : ∀ μ : Fin 4,
    (∑ a : Bool, ∑ b : Bool, firstKernel a b*dual μ a b) =
      if μ=0 ∨ μ=1 then 1 else 0 := by decide +kernel

theorem contract_reconstruct (K : Mat) (F : Fin 4 → Signature Scalar 4) :
    Signature.contract K (reconstruct F) = fun x =>
      ∑ μ : Fin 4, (∑ a : Bool, ∑ b : Bool, K a b*dual μ a b)*F μ x := by
  funext x
  change (∑ a : Bool, ∑ b : Bool, K a b*(∑ μ : Fin 4, dual μ a b*F μ x)) = _
  simp only [Finset.mul_sum]
  calc
    (∑ a : Bool, ∑ b : Bool, ∑ μ : Fin 4, K a b*(dual μ a b*F μ x)) =
        ∑ a : Bool, ∑ μ : Fin 4, ∑ b : Bool, K a b*(dual μ a b*F μ x) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul,mul_assoc]

theorem first_card_reconstruct (F : Fin 4 → Signature Scalar 4) :
    Signature.contract firstKernel (reconstruct F)=F 0+F 1 := by
  rw [contract_reconstruct]
  funext x
  simp only [firstKernel_dual]
  simp [Fin.sum_univ_succ]

theorem regular_card_exact (frame : Fin 4) (order : Fin 6) :
    Signature.contract firstKernel (reconstruct (fullImages frame order)) =
      regularCard (frames frame (permutations order 0)) := by
  rw [first_card_reconstruct]
  rfl

theorem pairKernel_theta (f : Form) (K : Mat) :
    pairKernel (mt (conjugator f)) (inverseConjugator f) (theta f K)=K := by
  simp only [pairKernel,kernel_mul_eq_mm,Kernel.transpose,mt]
  change mm (conjugator f) (mm (theta f K) (inverseConjugator f))=K
  simp only [theta]
  rw [← mm_assoc,← mm_assoc,(conjugator_inverses f).1,q0_mm,
    mm_assoc,(conjugator_inverses f).1,mm_q0]

theorem full_card_exact (f : Form) (frame : Fin 4) (order : Fin 6) :
    Signature.contract (theta f firstKernel) (fullAncestor f frame order)=
      coefficientCard f (Fin.castAdd 6 (frames frame (permutations order 0))) := by
  unfold fullAncestor
  rw [contract_action]
  change Signature.coordinateAction (coefficientLegs f)
      (Signature.contract (pairKernel (mt (conjugator f)) (inverseConjugator f)
        (theta f firstKernel)) (reconstruct (fullImages frame order))) = _
  rw [pairKernel_theta,regular_card_exact]
  simp only [coefficientCard,baseCard,Fin.addCases_left]

theorem deficient_reindex_legs (f : Form) :
    (fun j => sixLegs f ((Holant.Certificates.TetrahedralDeck.portOrder 1) j))=sixLegs f := by
  funext j
  fin_cases j <;> rfl

theorem deficient_card_exact (f : Form) (order : Fin 6) :
    Signature.contract (q 0)
      (Tensor.reindex (Holant.Certificates.TetrahedralDeck.portOrder 1).symm
        (deficientAncestor f order)) = coefficientCard f (Fin.natAdd 9 order) := by
  unfold deficientAncestor
  rw [reindex_action,Equiv.symm_symm,deficient_reindex_legs,contract_action]
  have hK : pairKernel (mt (conjugator f)) (inverseConjugator f) (q 0)=q 0 := by
    have ht : theta f (q 0)=q 0 := by
      simp only [theta,q0_mm]
      exact (conjugator_inverses f).2
    simpa only [ht] using pairKernel_theta f (q 0)
  change Signature.coordinateAction (coefficientLegs f)
      (Signature.contract (pairKernel (mt (conjugator f)) (inverseConjugator f) (q 0)) _) = _
  rw [hK]
  simp only [coefficientCard,baseCard,Fin.addCases_right,deficientCard]

def corrections (f : Form) : Fin 4 → Mat := ![q 0,correction f,q 0,correction f]

theorem corrections_exact (f : Form) (r : Fin 15) :
    Signature.coordinateAction (corrections f) (coefficientCard f r)=correctedCard f r := by
  unfold coefficientCard correctedCard
  rw [Signature.coordinateAction_comp]
  congr 1
  funext j
  rw [kernel_mul_eq_mm]
  fin_cases j <;> simp [corrections,coefficientLegs,correction_cancels]

end Holant.Certificates.OctahedralSeparator
