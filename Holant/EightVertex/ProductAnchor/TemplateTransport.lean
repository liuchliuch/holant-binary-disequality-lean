import Holant.EightVertex.ProductAnchor.DenseNormalization
import Holant.ReedMuller.CoefficientAtlas.ContractionTransport
import Holant.Tractable.KPresentation

/-! Ordered one/two-copy templates and exact bilinear coordinate transport.
All contractions are the literal native kernels; no coordinate matrix is a
physical vertex. -/
namespace Holant.EightVertex.ProductAnchor
open Holant.Tractable Holant.Certificates.FourthRootOdd
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def splitWords (m n : ℕ) : (Fin (m+n) → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) Bool)

 theorem coordinateAction_tensor {K : Type*} [CommSemiring K] {m n : ℕ}
    (A : Kernel K) (f : Signature K m) (g : Signature K n) :
    Signature.coordinateAction (fun _ => A) (Signature.tensor f g)=
      Signature.tensor (Signature.coordinateAction (fun _ => A) f)
        (Signature.coordinateAction (fun _ => A) g) := by
  funext x
  simp only [Signature.coordinateAction,Signature.tensor_apply]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [←Fintype.sum_prod_type']
  apply Fintype.sum_equiv (splitWords m n)
  intro y
  rw [Fin.prod_univ_add]
  change _ = ((∏ j, A (x (Fin.castAdd n j)) (y (Fin.castAdd n j))) * f (fun j => y (Fin.castAdd n j))) *
    ((∏ j, A (x (Fin.natAdd m j)) (y (Fin.natAdd m j))) * g (fun j => y (Fin.natAdd m j)))
  ring

 def anchorTemplate (E : Mat) (s : Word4) (q : Signature Scalar 4) : Signature Scalar 4 :=
  if Holant.weight s=0 ∨ Holant.weight s=4 then q else
    Signature.contract E (Signature.contract E
      (Tensor.reindex (wiringEquiv s).symm (Signature.tensor q q)))

 theorem pullback_forward (R : InvertibleKernel)
    (hR : Kernel.pullback Signature.disequality R.inverse=Signature.equality) :
    Kernel.pullback Signature.equality R.matrix=Signature.disequality := by
  rw [←hR,←pullback_mul,R.inverse_matrix]
  simp [Kernel.pullback]

 theorem action_contract_native (R : InvertibleKernel)
    (hR : Kernel.pullback Signature.disequality R.inverse=Signature.equality)
    {n : ℕ} (q : Signature Scalar (n+2)) :
    R.action (Signature.contract Signature.disequality q)=
      Signature.contract Signature.equality (R.action q) := by
  symm
  change Signature.contract Signature.equality (Signature.coordinateAction (fun _ => R.matrix) q)=_
  rw [ReedMuller.CoefficientAtlas.coordinateAction_contract,pullback_forward R hR]
  rfl

 theorem action_anchorTemplate (R : InvertibleKernel)
    (hR : Kernel.pullback Signature.disequality R.inverse=Signature.equality)
    (s : Word4) (q : Signature Scalar 4) :
    R.action (anchorTemplate Signature.disequality s q)=
      anchorTemplate Signature.equality s (R.action q) := by
  unfold anchorTemplate
  split
  · rfl
  · rw [action_contract_native R hR,action_contract_native R hR]
    unfold InvertibleKernel.action
    rw [ReedMuller.CoefficientAtlas.coordinateAction_reindex,
      coordinateAction_tensor (m := 4) (n := 4) R.matrix q q]

 theorem normalizedNetwork_template (s : Word4) :
    (normalizedNetwork (K := Scalar) s).denote=anchorTemplate Signature.equality s (normalized s) := by
  unfold normalizedNetwork anchorTemplate
  split
  · exact Network.denote_corolla _
  · rw [twoCopyNetwork,Network.denote_contract,Network.denote_contract,
      reorderNetwork_denote,pairCorolla_denote]

 theorem normalized_template (s : Word4) :
    anchorTemplate Signature.equality s (normalized s)=
      fun x => outputScalar s*equalityFour x := by
  rw [←normalizedNetwork_template]
  exact normalizedNetwork_denote s

 theorem contract_scale {n : ℕ} (E : Mat) (c : Scalar) (q : Signature Scalar (n+2)) :
    Signature.contract E (fun x => c*q x)=fun x => c*Signature.contract E q x := by
  funext x
  simp only [Signature.contract,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

 def templateCopies (s : Word4) : ℕ := if Holant.weight s=0 ∨ Holant.weight s=4 then 1 else 2

 theorem anchorTemplate_scale (E : Mat) (s : Word4) (q : Signature Scalar 4) (c : Scalar) :
    anchorTemplate E s (fun x => c*q x)=fun x => c^(templateCopies s)*anchorTemplate E s q x := by
  unfold anchorTemplate templateCopies
  split
  · simp
  · have h : Signature.tensor (fun x => c*q x) (fun x => c*q x)=
        (fun x => c^2*Signature.tensor q q x) := by
      funext x
      simp only [Signature.tensor_apply]
      ring
    rw [h]
    change Signature.contract E (Signature.contract E (fun x => c^2*
      (Tensor.reindex (wiringEquiv s).symm (Signature.tensor q q)) x))=_
    rw [contract_scale,contract_scale]

 theorem dense_native_template_normalized (q : Signature Scalar 4) (h : DenseForm q) :
    ∃ (R : InvertibleKernel) (s : Word4) (c : Scalar),c≠0 ∧
      Kernel.pullback Signature.disequality R.inverse=Signature.equality ∧
      R.action (anchorTemplate Signature.disequality s q)=(fun x => c*equalityFour x) := by
  obtain ⟨R,eta,s,heta,hR,hq⟩ := dense_normal_form q h
  refine ⟨R,s,eta^(templateCopies s)*outputScalar s,
    mul_ne_zero (pow_ne_zero _ heta) (outputScalar_ne_zero s),hR,?_⟩
  rw [action_anchorTemplate R hR,hq,anchorTemplate_scale,normalized_template]
  funext x
  ring

end
end Holant.EightVertex.ProductAnchor
