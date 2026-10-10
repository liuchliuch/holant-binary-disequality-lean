import Holant.Certificates.AffineEndpoint.BaseCoverage
import Holant.Certificates.AffineEndpoint.CoreAssembly

/-! Full Theorem A.4, authoritative paper1.tex lines15768–15791. The finite
input family is derived from genuine Affine witnesses, the two base sweeps are
kernel checked, and exact core covariance covers all eighteen literal matrices.
No retained-list or normal-form coverage hypothesis is supplied by the caller. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem all_core_normal_form (k : CoreIndex) (f : Signature AlgebraicComplex 4)
    (hf : Affine f) (hn : f≠0) (hg : EndpointEven (coreAction k f)) :
    EndpointNormalForm (coreAction k f) :=
  core_normal_form_of_base_coverage BaseCertificate.all_base_inputs k f hf hn hg

/-- A stronger direct-use version permits any nonzero affine scale at input. -/
 theorem source_A4_normal_form (f : Signature AlgebraicComplex 4) (hf : Affine f) (hn : f≠0)
    (K : Matrix Bool Bool AlgebraicComplex) (hK : SourceCore K)
    (hodd : ∀x,Holant.weight x%2=1→Signature.coordinateAction (fun _ => K) f x=0)
    (hends : Signature.coordinateAction (fun _ => K) f zeroWord*
      Signature.coordinateAction (fun _ => K) f oneWord≠0) :
    EndpointNormalForm (Signature.coordinateAction (fun _ => K) f) := by
  obtain ⟨k,rfl⟩ := source_core_complete K hK
  exact all_core_normal_form k f hf hn ⟨(mul_ne_zero_iff.mp hends).1,(mul_ne_zero_iff.mp hends).2,hodd⟩

/-- The exact eighteen-element core clause and all normalized-input clauses
of the printed theorem, with actual algebraic nonzero scale and diagonal entry. -/
 theorem source_A4 :
    {K : Matrix Bool Bool AlgebraicComplex | SourceCore K}.ncard=18 ∧
    ∀f : Signature AlgebraicComplex 4,Affine f→f≠0→CanonicalNormalized f→
    ∀K : Matrix Bool Bool AlgebraicComplex,SourceCore K→
    (∀x,Holant.weight x%2=1→Signature.coordinateAction (fun _ => K) f x=0)→
    Signature.coordinateAction (fun _ => K) f zeroWord*
      Signature.coordinateAction (fun _ => K) f oneWord≠0→
    EndpointNormalForm (Signature.coordinateAction (fun _ => K) f) :=
  ⟨source_core_count,fun f hf hn _ K hK hodd hends => source_A4_normal_form f hf hn K hK hodd hends⟩

 theorem source_A4_support_cases (h : Signature AlgebraicComplex 4) (hs : AffineReference.ReferenceSupport h) :
    AffineReference.supportSize h=2 ∨ AffineReference.supportSize h=4 ∨ AffineReference.supportSize h=8 := by
  rcases hs with he|⟨b,hb⟩|hf
  · exact Or.inl (AffineReference.endpoint_support_size h he)
  · exact Or.inr (Or.inl (AffineReference.plane_support_size h b hb))
  · exact Or.inr (Or.inr (AffineReference.full_even_support_size h hf))

end
end Holant.Certificates.AffineEndpoint
