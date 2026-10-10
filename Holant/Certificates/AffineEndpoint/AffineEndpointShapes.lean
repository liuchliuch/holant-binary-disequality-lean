import Holant.Certificates.AffineEndpoint.References

/-! Endpoint-nondegenerate even affine signatures already have precisely the
three source support types. This clause is structural after support coverage. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Tractable.AffinePhase SupportCatalog
open Holant.EightVertex.ProductAnchor Holant.Certificates.AffineReference
open Holant.Certificates.FourthRootOdd
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

 theorem endpoint_support_shapes : ∀s : SupportIndex,
    zeroWord∈supportWords s → oneWord∈supportWords s →
    (∀x,Holant.weight x%2=1→x∉supportWords s)→
    (∀x,x∈supportWords s ↔ x=zeroWord ∨ x=oneWord) ∨
    (∃b : Fin 3,∀x,x∈supportWords s ↔ OnPlane b x) ∨
    (∀x,x∈supportWords s ↔ evenWord x=true) := by decide +kernel

end
end Holant.Certificates.AffineEndpoint
