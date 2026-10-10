import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralDressing
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralInverseTransport

/-! Two actual current binary-dressing stages reduce an arbitrary rank-two
map to its same-row baseline. The old image, adjoint, and harmonic parameter
are produced internally, and every comparison scalar remains nonzero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralNormalized
open Holant Holant.Tractable Holant.Algebraic Holant.Projective.BoundedTorsion
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.TetrahedralPreservers
open Holant.Certificates.MatchingProductBridge
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry
open Preserver RankTwo.QuotientEnumeration RankTwo.PhysicalOrbit
open ClosureMarkedDihedral.Source
open scoped BigOperators Matrix
namespace D
export GlobalCloseCompletionOctahedralDressing (Tensor ψ targetSlots transport_slots)
end D

abbrev prototype (f : Form) : FourTensor :=
  reconstruct (rightX*RankTwo.HarmonicProjectivities.model f baseCode baseCode 0)

theorem action_smul {K : Type*} [CommSemiring K] {n : ℕ}
    (A : Fin n→Kernel K) (q : Signature K n) (c : K) :
    Signature.coordinateAction A (c • q)=c • Signature.coordinateAction A q := by
  funext x
  simp only [Signature.coordinateAction,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)
variable (f : Form)
variable (literal : group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group f)

include literal in
theorem canonical (Q : D.Tensor G P)
    (twoSided : TwoSided (Roots f) (transferMatrix (RingHomRealization.mapSignature (D.ψ G) Q.table) (Equiv.refl _)))
    (rankTwo : (transferMatrix (RingHomRealization.mapSignature (D.ψ G) Q.table) (Equiv.refl _)).rank=2) :
    ∃ R : D.Tensor G P,∃ c : ℂ,c≠0 ∧ RingHomRealization.mapSignature (D.ψ G) R.table=c • prototype f := by
  let A := transferMatrix (RingHomRealization.mapSignature (D.ψ G) Q.table) (Equiv.refl _)
  obtain ⟨l,r,paired⟩ := rank_two_paired_ranges f A twoSided rankTwo
  obtain ⟨k,c,hc,hcmap⟩ := normalize_class f A l r paired
  obtain ⟨Q₁,α,hα,h₁⟩ := D.transport_slots G P tau f literal Q
    (inverseCodes f l.val r.val) inverseReverse (inverseSlots f l.val r.val)
    (inverseSlotScale f l.val r.val) (inverseSlotScale_ne f l.val r.val)
    (inverseSlots_scale f l.val r.val)
  obtain ⟨Q₂,β,hβ,h₂⟩ := D.transport_slots G P tau f literal Q₁
    (stabilizerInverseCodes f k) stabilizerInverseReverse (stabilizerInverseSlots f k)
    (stabilizerInverseScale f k) (stabilizerInverseScale_ne f k)
    (stabilizerInverseSlots_scale f k)
  have haction : Signature.coordinateAction (stabilizerInverseSlots f k)
      (Signature.coordinateAction (inverseSlots f l.val r.val) (RingHomRealization.mapSignature (D.ψ G) Q.table))=
        c • prototype f := by
    rw [inverse_tensor,stabilizer_inverse_tensor,transfer_reconstruct]
    change reconstruct ((rightX*inverseStabilizer f k)*normalizedMap f A l.val r.val)=_
    rw [Matrix.mul_assoc,hcmap,Matrix.mul_smul,RankTwo.HarmonicProjectivities.reconstruct_smul]
  refine ⟨Q₂,β*(α*c),mul_ne_zero hβ (mul_ne_zero hα hc),?_⟩
  rw [h₂,h₁,action_smul,haction,smul_smul,smul_smul,mul_assoc]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralNormalized
end
