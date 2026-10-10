import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralNormalized
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralMixedEndpoints

/-! All four actual marked rows reach their literal terminal shapes by the
original allowed binary slots. dd/tt use two further stages; dt/td use one.
Primality and source realization are transported at every physical stage. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralTerminals
open Holant Holant.Tractable Holant.Algebraic Holant.Projective.BoundedTorsion
open Holant.Certificates Holant.Certificates.OctahedralSeparator
open Holant.Certificates.TetrahedralPreservers
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry
open Preserver RankTwo.PhysicalOrbit RankTwo.BaseTerminals RankTwo.CanonicalEndpointBridge
open ClosureMarkedDihedral.Source
open GlobalCloseCompletionOctahedralNormalized
open scoped BigOperators Matrix
namespace D
export GlobalCloseCompletionOctahedralDressing (Tensor ψ targetSlots transport_slots)
end D
namespace M
export RankTwo.MixedEndpointBridge
  (mixedRow mixedCodes mixedPorts mixedShape exteriorScale physical_slots mixed_complex_exact
   exteriorScale_ne shape_zero shape_one shape_odd phaseValue)
end M

abbrev EndpointComplex (q : Signature ℂ 4) : Prop :=
  q (fun _=>false)≠0 ∧ q (fun _=>true)≠0 ∧ ∀x,Holant.weight x%2=1 → q x=0

def target (f : Form) : Signature ℂ 4 :=
  if f=0 then terminalShape false else if f=1 then terminalShape true else
    if f=2 then M.mixedShape false Complex.I else M.mixedShape true Complex.I

theorem target_endpoint (f : Form) : EndpointComplex (target f) := by
  have base (b : Bool) : EndpointComplex (terminalShape b) :=
    ⟨by rw [shape_zero]; exact one_ne_zero,
     by rw [shape_one]; exact one_ne_zero,shape_odd b⟩
  have mixed (b : Bool) : EndpointComplex (M.mixedShape b Complex.I) := by
    refine ⟨by rw [M.shape_zero]; exact one_ne_zero,?_,M.shape_odd b Complex.I⟩
    rw [M.shape_one]
    cases b <;> simp [M.phaseValue,Complex.I_ne_zero]
  fin_cases f
  · simpa [target] using base false
  · simpa [target] using base true
  · simpa [target] using mixed false
  · simpa [target] using mixed true

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)

private theorem base_terminal (b : Bool)
    (literal : group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group (baseForm b))
    (Q : D.Tensor G P) (c : ℂ) (hc : c≠0)
    (hQ : RingHomRealization.mapSignature (D.ψ G) Q.table=c • GlobalCloseCompletionOctahedralNormalized.prototype (baseForm b)) :
    ∃ R : D.Tensor G P,∃ d : ℂ,d≠0 ∧ RingHomRealization.mapSignature (D.ψ G) R.table=d • terminalShape b := by
  obtain ⟨Q₁,α,hα,h₁⟩ := D.transport_slots G P tau (baseForm b) literal Q
    (correctionCodes (baseForm b)) correctionReverse
    (fun i=>complexMatrix (correctionPorts (baseForm b) i))
    (correctionSlotScale (baseForm b)) (correctionSlotScale_ne (baseForm b))
    (correction_slots (baseForm b))
  have hp : RingHomRealization.mapSignature (D.ψ G) Q₁.table=(α*c) • complexBase b := by
    rw [h₁,hQ,action_smul,prototype_correction,smul_smul]
  have slots : complexLegs b=fun i=>(1 : ℂ) • D.targetSlots (baseForm b) (baseCodes b) baseReverse i := by
    funext i
    simp [complexLegs,paletteLegs,D.targetSlots,baseReverse,kernel]
  obtain ⟨Q₂,β,hβ,h₂⟩ := D.transport_slots G P tau (baseForm b) literal Q₁
    (baseCodes b) baseReverse (complexLegs b) (fun _=>1) (fun _=>one_ne_zero) slots
  refine ⟨Q₂,β*((α*c)*complexScale b),
    mul_ne_zero hβ (mul_ne_zero (mul_ne_zero hα hc) (complexScale_ne b)),?_⟩
  rw [h₂,hp,action_smul,complex_exact,complexTerminal_shape,smul_smul,smul_smul,mul_assoc]

private theorem mixed_terminal (b : Bool)
    (literal : group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group (M.mixedRow b))
    (Q : D.Tensor G P) (c : ℂ) (hc : c≠0)
    (hQ : RingHomRealization.mapSignature (D.ψ G) Q.table=c • GlobalCloseCompletionOctahedralNormalized.prototype (M.mixedRow b)) :
    ∃ R : D.Tensor G P,∃ d : ℂ,d≠0 ∧ RingHomRealization.mapSignature (D.ψ G) R.table=d • M.mixedShape b Complex.I := by
  obtain ⟨R,α,hα,hR⟩ := D.transport_slots G P tau (M.mixedRow b) literal Q
    (M.mixedCodes b) correctionReverse (fun i=>complexMatrix (M.mixedPorts b i))
    (correctionSlotScale (M.mixedRow b)) (correctionSlotScale_ne (M.mixedRow b))
    (M.physical_slots b)
  refine ⟨R,α*(c*embed (M.exteriorScale b)),
    mul_ne_zero hα (mul_ne_zero hc (embed_ne_zero (M.exteriorScale_ne b))),?_⟩
  rw [hR,hQ,action_smul,M.mixed_complex_exact,smul_smul,smul_smul,mul_assoc]

theorem from_canonical (f : Form)
    (literal : group (ClosureSourceRows.embedding G) P.family tau=Coordinates.Models.group f)
    (Q : D.Tensor G P) (c : ℂ) (hc : c≠0)
    (hQ : RingHomRealization.mapSignature (D.ψ G) Q.table=c • GlobalCloseCompletionOctahedralNormalized.prototype f) :
    ∃ R : D.Tensor G P,∃ d : ℂ,d≠0 ∧ RingHomRealization.mapSignature (D.ψ G) R.table=d • target f := by
  fin_cases f
  · simpa [target,baseForm,M.mixedRow] using base_terminal G P tau false literal Q c hc hQ
  · simpa [target,baseForm,M.mixedRow] using base_terminal G P tau true literal Q c hc hQ
  · simpa [target,baseForm,M.mixedRow] using mixed_terminal G P tau false literal Q c hc hQ
  · simpa [target,baseForm,M.mixedRow] using mixed_terminal G P tau true literal Q c hc hQ

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralTerminals
end
