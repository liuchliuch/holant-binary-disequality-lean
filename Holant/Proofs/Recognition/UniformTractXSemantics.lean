import Holant.Proofs.Recognition.UniformTensorDecisionBranch
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineRecognitionSource
import Holant.Proofs.Algorithms.TransformRecognition.RawProductRecognitionSource
import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineRecognitionSource
import Holant.Proofs.Algorithms.TractXRestore

/-!
# Exact positive and negative meanings of all four reduced-criterion decisions

The old A/P/L machines decide complex polynomial systems. This module proves
both directions between those actual answers and the algebraic source common-
basis predicates. In particular the reverse direction is proved by lifting
an existing algebraic solution, not assumed from a positive-only installer.
The public preprocessing convention is restored and removed in both directions.
-/

namespace Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTractXSemantics

open Holant Holant.Tractable MvPolynomial
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.MainChain.TransformRecognition
open UniformTensorDecisionBranch
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {σ : Type*}

theorem eval_lift (p : MvPolynomial σ AlgebraicComplex) (z : σ → AlgebraicComplex) :
    eval₂ (algebraMap AlgebraicComplex ℂ) (fun i => (z i : ℂ)) p =
      (algebraMap AlgebraicComplex ℂ) (eval₂ (RingHom.id AlgebraicComplex) z p) := by
  simpa only [RingHom.comp_id,Function.comp_def,IntermediateField.algebraMap_apply] using
    (MvPolynomial.eval₂_comp_left (algebraMap AlgebraicComplex ℂ)
      (RingHom.id AlgebraicComplex) z p).symm

variable {s : ℕ} {arity : Fin s → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i)) (E : Kernel AlgebraicComplex)

theorem affine_lift (h : AffineBranch.Shared G E (RingHom.id AlgebraicComplex)) :
    AffineBranch.Shared G E (algebraMap AlgebraicComplex ℂ) := by
  obtain ⟨B,z,hz⟩ := AffineBranch.solution_of_shared G E (RingHom.id AlgebraicComplex) h
  apply AffineBranch.shared_of_solution G E (algebraMap AlgebraicComplex ℂ) B (fun i => (z i : ℂ))
  intro r
  rw [eval_lift,hz r,map_zero]

theorem product_lift (h : ProductBranch.SharedTemplates G E (RingHom.id AlgebraicComplex)) :
    ProductBranch.SharedTemplates G E (algebraMap AlgebraicComplex ℂ) := by
  obtain ⟨B,z,hz⟩ := ProductBranch.solution_of_templates G E (RingHom.id AlgebraicComplex) h
  apply ProductBranch.templates_of_solution G E (algebraMap AlgebraicComplex ℂ) B (fun i => (z i : ℂ))
  intro r
  rw [eval_lift,hz r,map_zero]

theorem localAffine_lift (h : LocalAffineBranch.Shared G E (RingHom.id AlgebraicComplex)) :
    LocalAffineBranch.Shared G E (algebraMap AlgebraicComplex ℂ) := by
  obtain ⟨B,z,he,hn⟩ := LocalAffineBranch.solution_of_shared G E (RingHom.id AlgebraicComplex) h
  apply LocalAffineBranch.shared_of_solution G E (algebraMap AlgebraicComplex ℂ) B
    (fun i => (z i : ℂ))
  · intro r
    rw [eval_lift,he r,map_zero]
  · intro r
    rw [eval_lift]
    exact fun h => hn r (Subtype.ext h)

variable (arity)

theorem valid (d : Data s arity) : OriginalFamilyInput.Valid arity d.input := ⟨d.G,d.represented⟩

def affine (d : Data s arity) : Bool := RawAffineRecognitionSource.answer arity d.input (valid arity d) false
def product (d : Data s arity) : Bool := RawProductRecognitionSource.answer arity d.input (valid arity d) false
def localAffine (d : Data s arity) : Bool := RawLocalAffineRecognitionSource.answer arity d.input (valid arity d) false

theorem affine_correct (d : Data s arity) :
    affine arity d = true ↔ CommonTransformable affineClass (AffineBranch.indexedFamily d.G) := by
  rw [affine,RawAffineRecognitionSource.answer_correct arity d.input (valid arity d) false d.G d.represented,
    AffineBranch.common_iff_shared]
  change AffineBranch.Shared d.G Signature.equality (algebraMap AlgebraicComplex ℂ) ↔ _
  exact ⟨AffineBranch.descend d.G Signature.equality,affine_lift d.G Signature.equality⟩

theorem product_correct (d : Data s arity) :
    product arity d = true ↔ CommonTransformable productClass (AffineBranch.indexedFamily d.G) := by
  rw [product,RawProductRecognitionSource.answer_correct arity d.input (valid arity d) false d.G d.represented,
    ProductBranch.common_iff_templates]
  change ProductBranch.SharedSource d.G Signature.equality (algebraMap AlgebraicComplex ℂ) ↔ _
  rw [ProductBranch.source_iff_templates]
  exact ⟨ProductBranch.descend_templates d.G Signature.equality,product_lift d.G Signature.equality⟩

theorem localAffine_correct (d : Data s arity) :
    localAffine arity d = true ↔ CommonTransformable localAffineClass (AffineBranch.indexedFamily d.G) := by
  rw [localAffine,RawLocalAffineRecognitionSource.answer_correct arity d.input (valid arity d) false d.G d.represented,
    LocalAffineBranch.common_iff_shared]
  change LocalAffineBranch.Shared d.G Signature.equality (algebraMap AlgebraicComplex ℂ) ↔ _
  exact ⟨LocalAffineBranch.descend d.G Signature.equality,localAffine_lift d.G Signature.equality⟩

/-- The four core alternatives descend to the prescribed retained subfamily. -/
theorem core_preprocess {F : SignatureFamily AlgebraicComplex} (h : TractXCore F) :
    TractXCore (preprocess F) := by
  have hsub : preprocess F ⊆ F := fun _ hf => hf.1
  rcases h with h | h | h | h
  · exact Or.inl (h.mono_family hsub)
  · exact Or.inr (Or.inl (h.mono_family hsub))
  · exact Or.inr (Or.inr (Or.inl (h.mono_family hsub)))
  · exact Or.inr (Or.inr (Or.inr (h.mono_family hsub)))

theorem tractX_iff_core (d : Data s arity) :
    TractX (AffineBranch.indexedFamily d.G) ↔ TractXCore (AffineBranch.indexedFamily d.G) := by
  constructor
  · exact TractXRestore.source_criterion_core (Set.finite_range _)
  · intro h
    exact ⟨(Set.finite_range _).subset (fun _ hf => hf.1),core_preprocess h⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.UniformTractXSemantics
