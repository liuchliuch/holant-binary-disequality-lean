import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalEvenCharacterPhase
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalRankOneCriterion
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedSignedSource

/-! The even-character LocalAffine supplier has no support-rank bound. Its
weighted signed restriction is an actual even original-label block, and a
hypothetical Affine output would certify every supported local twist. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalEvenCharacter
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXLocalEvenCharacterPhase (gauge gauge_affine gauge_nonzero split)
export NoXLocalSignedMultiplicityPhase (original unitPhase)
end P
namespace W
export NoXWeightedSignedPorts (weight table)
end W
namespace I
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end I
namespace S
export NoXWeightedSignedSource (evenBlock signature ambient_value)
end S
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n m r : ℕ}
section Semantic
variable {f : Signature AlgebraicComplex n}
variable (D : SystematicSupport f r) (ps : Fin n→Port m)
variable (code : Word r→Word m) (code_affine : TwoTranslate.IsAffineMap code)
variable (chart : ∀x,word ps (code x)=D.encode x)
variable (even : ∀j,Even (I.bundleSize ps j))
variable (v w : AlgebraicComplex) (hv : v≠0) (hw : w≠0) (fourth : v^4= -(w^4))

private def twistChart (a : Word r) : SystematicSupport (localTwist (D.encode a) f) r where
  ports := D.ports
  injective := D.injective
  encode := D.encode
  affine := D.affine
  free := D.free
  supported x := (NoXLocalRankOneCriterion.twist_support f (D.encode a) _).mpr (D.supported x)
  covers x hx := D.covers x ((NoXLocalRankOneCriterion.twist_support f (D.encode a) _).mp hx)

include code_affine chart even hv hw fourth in
theorem local_of_weighted (square : Affine (fun x=>f x^2))
    (weighted : Affine (fun z=>W.weight v w ps z*f (word ps z))) : LocalAffine f := by
  have nonzero : f≠0 := by intro hz;exact D.supported (origin _) (congrFun hz _)
  obtain ⟨system,hsystem⟩ := OrdinaryNegativeAffineSquareSupport.exists_support_system f square nonzero
  intro alpha supported
  let a : Word r := fun i=>alpha (D.ports i)
  have ha : D.encode a=alpha := D.covers alpha supported
  rw [←ha]
  apply (twistChart D a).affine_of_reduced system
  · intro x
    exact (hsystem x).trans (NoXLocalRankOneCriterion.twist_support f (D.encode a) x).symm
  · have hg := (P.gauge_affine v w fourth hv hw ps even (code a)).precompose code code_affine
    have hgInv := OrdinaryNegativeAffineSquareReciprocal.affine_inverse _ hg
    have actual := hgInv.mul (weighted.precompose code code_affine)
    convert actual using 1
    funext x
    change localTwist (D.encode a) f (D.encode x)=
      (P.gauge v w ps (code a) (code x))⁻¹*(W.weight v w ps (code x)*f (word ps (code x)))
    rw [chart,P.split v w ps (code a) (code x),localTwist_apply]
    have phase : P.original ps (code a) (code x)=
        ∏i,if D.encode a i && D.encode x i then zetaEight else 1 := by
      simp only [P.original,P.unitPhase,chart]
    rw [←phase]
    simp only [mul_assoc]
    rw [←mul_assoc (P.gauge v w ps (code a) (code x))⁻¹
      (P.gauge v w ps (code a) (code x)),
      inv_mul_cancel₀ (P.gauge_nonzero v w hv hw ps (code a) (code x)),one_mul]

end Semantic

section Actual
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
local instance : Algebra ℚ K := K.algebra'
variable (H : (i : Fin s)→Signature K (b i.val)) (j : Fin s) (labels : Fin 4→Fin s)
variable (v w : K)
variable (literal : ∀i,(⟨b (labels i).val,H (labels i)⟩ : AnySignature K)=
  ⟨OrdinaryNegativeSignedPortsCore.arity (b j.val) i.val,W.table (H j) v w i⟩)
variable (hv : v≠0) (hw : w≠0) (fourth : (v : AlgebraicComplex)^4= -((w : AlgebraicComplex)^4))
variable (D : SystematicSupport (fun z=>(H j z : AlgebraicComplex)) r)
variable (ps : Fin (b j.val)→Port m)
variable (code : Word r→Word m) (code_affine : TwoTranslate.IsAffineMap code)
variable (chart : ∀x,word ps (code x)=D.encode x)
variable (even : ∀q,Even (I.bundleSize ps q))
variable (square : Affine (fun z=>(H j z : AlgebraicComplex)^2))
variable (bad : ¬LocalAffine (fun z=>(H j z : AlgebraicComplex)))

include code_affine literal hv hw fourth chart even square bad in
theorem evenBad : OrdinaryNegativeXUniversalResource.EvenBad H := by
  refine ⟨m,S.evenBlock H labels (H j) v w literal ps even,?_⟩
  intro affine
  change Affine (fun z=>(S.signature H labels (H j) v w literal ps z : AlgebraicComplex)) at affine
  simp only [S.ambient_value] at affine
  exact bad (local_of_weighted D ps code code_affine chart even (v : AlgebraicComplex) (w : AlgebraicComplex)
    (fun h=>hv (Subtype.ext h)) (fun h=>hw (Subtype.ext h)) fourth square affine)
end Actual


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalEvenCharacter
end
