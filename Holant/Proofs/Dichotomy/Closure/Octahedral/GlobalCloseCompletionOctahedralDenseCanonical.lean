import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralActualBinary
import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBDenseCanonical

/-! The exact dense endpoints use the same canonical Eq4 matrix and an
actual binary from their marked O group. Both scalars remain explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralDenseCanonical
open Holant Holant.Tractable Holant.Marked Holant.Algebraic
open Holant.Projective.BoundedTorsion
open Holant.Certificates.OctahedralSeparator
open Holant.EightVertex.ProductAnchor
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry
open ClosureMarkedDihedral.Source
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family) (f : Form)
variable (literal : group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group f)

private theorem normalized_zero :
    (normalized (fun _=>false) : Signature AlgebraicComplex 4)=equalityFour := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [normalized,equalityFour,Holant.weight,Fin.sum_univ_four,funext_iff,
      Fin.forall_fin_succ,h0,h1,h2,h3]

include literal in
theorem of_dense (c r : AlgebraicComplex) (hc : c≠0) (hr : r≠0) (eighth : r^8=1)
    (actual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality
      (denseTensor c r (fun _=>false)))
    (phase : Direction f (Matrix.map (Holant.Marked.R (-(r^2)))
      (algebraicClosure ℚ ℂ).val.toRingHom)) :
    Nonempty (GlobalCloseCompletionBDenseCanonical.Canonical (ClosureSourceRows.ambientFamily G P)) := by
  obtain ⟨u,hu,hsq⟩ := exists_algebraic_normalizing_root r hr
  obtain ⟨mu,hm,ha⟩ := GlobalCloseCompletionOctahedralActualBinary.actual_scaled
    G P tau f literal (Holant.Marked.R (-(r^2))) (by rfl) phase
  refine ⟨⟨r,hr,eighth,u,hu,hsq,denseTensor c r (fun _=>false),actual,
    denseNormalizationScale c u (fun _=>false),denseNormalizationScale_ne_zero _ _ _ hc hu,
    ?_,kernelSignature (mu • Holant.Marked.R (-(r^2))),ha,mu*imaginaryUnit*r,
    mul_ne_zero (mul_ne_zero hm imaginaryUnit_ne_zero) hr,?_⟩⟩
  · change Signature.coordinateAction (fun _=>normalizationMatrix r u)
      (denseTensor c r (fun _=>false))=_
    rw [normalize_denseTensor c r u hr,normalized_zero]
  · exact GlobalCloseCompletionBDenseAnchorX.normalization_phase_X r u mu hr hu hsq

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralDenseCanonical
end
