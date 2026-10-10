import Holant.Proofs.Tractability.EOEvaluation.EOConditionCertificate.Descriptors
import Holant.Proofs.Tetrahedral.TransformRecognition.ProductNormalForm.Polynomials


namespace Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.LiteralTemplates
open Holant.Tractable
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
open Descriptors
noncomputable section

def affineRows {n : ℕ} (f : Signature AlgebraicComplex n)
    (C : AffineNormalForm.Code n) (c : AlgebraicComplex) : List AlgebraicComplex :=
  (words n).map (fun x => f x-AffineNormalForm.formula C c x)

theorem affineRows_zero {n : ℕ} (f : Signature AlgebraicComplex n)
    (C : AffineNormalForm.Code n) (c : AlgebraicComplex) :
    (∀ r ∈ affineRows f C c, r=0) ↔ f=AffineNormalForm.formula C c := by
  constructor
  · intro h
    funext x
    exact sub_eq_zero.mp (h _ (List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩))
  · intro h r hr
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr
    exact sub_eq_zero.mpr (congrFun h x)

theorem affine_complete {n : ℕ} (f : Signature AlgebraicComplex n) :
    Affine f ↔ ∃ C ∈ FiniteBranchEnumeration.affineCodes n,
      ∃ c : AlgebraicComplex, ∀ r ∈ affineRows f C c, r=0 := by
  rw [AffineNormalForm.affine_iff]
  constructor
  · rintro ⟨C,c,h⟩
    exact ⟨C,FiniteBranchEnumeration.mem_affineCodes C,c,(affineRows_zero f C c).mpr h⟩
  · rintro ⟨C,_,c,h⟩
    exact ⟨C,c,(affineRows_zero f C c).mp h⟩

def productRows {n : ℕ} (f : Signature AlgebraicComplex n) (S : Skeleton n) :
    List (MvPolynomial (Parameter n) AlgebraicComplex) :=
  (words n).map (entryEquation f S)

theorem productRows_zero {n : ℕ} (f : Signature AlgebraicComplex n)
    (S : Skeleton n) (theta : Parameter n → AlgebraicComplex) :
    (∀ r ∈ productRows f S, MvPolynomial.eval theta r=0) ↔ f=evaluate S theta := by
  constructor
  · intro h
    funext x
    exact (entryEquation_zero_iff f S theta x).mp
      (h _ (List.mem_map.mpr ⟨x,SparseTransform.mem_allWords x,rfl⟩))
  · intro h r hr
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr
    exact (entryEquation_zero_iff f S theta x).mpr (congrFun h x)

theorem product_complete {n : ℕ} (f : Signature AlgebraicComplex n) :
    Product f ↔ ∃ S ∈ FiniteBranchEnumeration.productCodes n,
      ∃ theta : Parameter n → AlgebraicComplex,
        ∀ r ∈ productRows f S, MvPolynomial.eval theta r=0 := by
  rw [Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.product_iff]
  constructor
  · rintro ⟨S,theta,h⟩
    exact ⟨S,FiniteBranchEnumeration.mem_productCodes S,theta,(productRows_zero f S theta).mpr h⟩
  · rintro ⟨S,_,theta,h⟩
    exact ⟨S,theta,(productRows_zero f S theta).mp h⟩

end
end Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate.LiteralTemplates
