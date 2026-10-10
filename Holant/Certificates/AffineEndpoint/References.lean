import Holant.Certificates.AffineEndpoint.InputModel
import Holant.Certificates.AffineEndpoint.LayerInvariant

/-! All 612 literal source reference phases on the endpoint pair, the three
complementary two-block planes, and the full even support. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase SupportCatalog
open Holant.EightVertex.ProductAnchor Holant.Certificates.AffineReference
open Holant.Certificates.FourthRootOdd
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

 def referenceInput (r : Fin 612) : InputCode :=
  if h : r.val<4 then ⟨128,⟨r.val,h⟩⟩ else
  if h' : r.val<36 then ⟨204,⟨r.val-4,by change r.val-4<32; omega⟩⟩ else
  if h'' : r.val<68 then ⟨236,⟨r.val-36,by change r.val-36<32; omega⟩⟩ else
  if h''' : r.val<100 then ⟨248,⟨r.val-68,by change r.val-68<32; omega⟩⟩ else
  ⟨304,⟨r.val-100,by change r.val-100<512; omega⟩⟩

 noncomputable def reference (r : Fin 612) : Signature AlgebraicComplex 4 := inputSignature (referenceInput r)

 theorem reference_affine (r : Fin 612) : Affine (reference r) := inputSignature_affine _

 theorem reference_origins : ∀r,supportOrigin (referenceInput r).1=zeroWord := by decide +kernel
 theorem reference_origin (r : Fin 612) : reference r zeroWord=1 := by
  rw [←reference_origins r]
  exact inputSignature_origin _

 theorem reference_shapes : ∀r,
    (∀x,x∈supportWords (referenceInput r).1 ↔ x=zeroWord ∨ x=oneWord) ∨
    (∃b : Fin 3,∀x,x∈supportWords (referenceInput r).1 ↔ OnPlane b x) ∨
    (∀x,x∈supportWords (referenceInput r).1 ↔ evenWord x=true) := by decide +kernel

 theorem reference_support (r : Fin 612) : ReferenceSupport (reference r) := by
  have hs := inputSignature_support (referenceInput r)
  rcases reference_shapes r with he|⟨b,hb⟩|hf
  · exact Or.inl (fun x => (hs x).trans (he x))
  · exact Or.inr (Or.inl ⟨b,fun x => (hs x).trans (hb x)⟩)
  · exact Or.inr (Or.inr (fun x => (hs x).trans (hf x)))

 theorem reference_endpoint_support : ∀r,
    zeroWord∈supportWords (referenceInput r).1 ∧ oneWord∈supportWords (referenceInput r).1 ∧
    ∀x,Holant.weight x%2=1→x∉supportWords (referenceInput r).1 := by decide +kernel

 theorem reference_endpoint_even (r : Fin 612) : EndpointEven (reference r) := by
  have hs := inputSignature_support (referenceInput r)
  obtain ⟨h0,h1,ho⟩ := reference_endpoint_support r
  refine ⟨(hs _).mpr h0,(hs _).mpr h1,?_⟩
  intro x hx
  exact Classical.not_not.mp (fun hn => ho x hx ((hs x).mp hn))

 theorem endpoint_reference_central_zero : ∀i,reference 0 (centralWord i)=0 := by
  intro i
  have h : centralWord i∉supportWords (referenceInput 0).1 := by
    fin_cases i <;> decide +kernel
  exact Classical.not_not.mp (fun hn => h ((inputSignature_support _ _).mp hn))

 theorem endpoints_normal_form (g : Signature AlgebraicComplex 4) (hg : EndpointEven g)
    (hc : ∀i,g (centralWord i)=0) : EndpointNormalForm g := by
  obtain ⟨gamma,t,hgamma,ht,he⟩ := diagonal_form_of_endpoints g (reference 0) hg
    (reference_endpoint_even 0) hc endpoint_reference_central_zero
  exact ⟨gamma,t,hgamma,ht,reference 0,reference_affine 0,reference_origin 0,reference_support 0,he⟩

end Holant.Certificates.AffineEndpoint
