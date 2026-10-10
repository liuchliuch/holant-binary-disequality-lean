import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenBundlePhase
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalMasks
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffinePorts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateRows

/-! Every separately-even rank-three repair is non-Affine when the original
row is genuinely bad for LocalAffine and all proper pin masks are L. Each
correction contributes its supported Affine local twist; the entire recipe
has an Affine total local phase by its proved cumulative signed incidence. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankThreeBundle
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace A
export NoXReciprocalRankThreeAffinePorts (Transform input input_affine input_pin transformed transformed_code)
end A
namespace P
export OrdinaryNegativeSparseRankThreePorts (port word_code)
export NoXSeparateSignedProjection (signedCount)
export NoXLocalSignedMultiplicityPhase (original unitPhase)
end P
namespace C
export OrdinaryNegativeSparseMixingAlpha (codeSeven codeSeven_affine multiply_affine_core)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {n k : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 3)
variable (schedule : Fin k→A.Transform)

def rows : Fin (k+1)→Fin n→Port 7:=
  Fin.cases (P.port D) (fun i=>A.transformed (P.port D) (schedule i))
def core (a x : Word 3) : AlgebraicComplex:=localTwist (D.encode a) f (D.encode x)
def correction (a : Word 3) (i : Fin k) (x : Word 3) : AlgebraicComplex:=
  localTwist (D.encode (A.input (schedule i) a)) f (D.encode (A.input (schedule i) x))
def multiplier (a : Word 3) : Signature AlgebraicComplex 3:=fun x=>∏i,correction D schedule a i x

variable (masks : ∀i bit,LocalAffine (pinMask f (D.ports i) bit))
include masks in
theorem correction_affine (a : Word 3) (i : Fin k) : Affine (correction D schedule a i):=
  NoXGeneralLocalMasks.twisted_fixed D (A.input (schedule i)) (A.input_affine (schedule i))
    (schedule i).base.axis (OrdinaryNegativeSparseRankThreeParity.bits (schedule i).shift (schedule i).base.axis)
    (A.input_pin (schedule i)) (masks _ _) a

include masks in
theorem multiplier_affine (a : Word 3) : Affine (multiplier D schedule a):=
  Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization.affine_prod
    (correction D schedule a) (correction_affine D schedule masks a)

theorem multiplier_full (a x : Word 3) : multiplier D schedule a x≠0:=by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (NoXLocalRankOneCriterion.twist_support f _ _).mpr (D.supported _)

theorem value (a x : Word 3) :
    (∏v : Fin (k+1),P.original (rows D schedule v) (C.codeSeven a) (C.codeSeven x))*
      (∏v : Fin (k+1),f (word (rows D schedule v) (C.codeSeven x)))=
      core D a x*multiplier D schedule a x:=by
  rw [←Finset.prod_mul_distrib,Fin.prod_univ_succ]
  simp only [rows,Fin.cases_zero,Fin.cases_succ,core,multiplier,correction,
    P.original,P.unitPhase,P.word_code,A.transformed_code,localTwist_apply]

variable (square : Affine (fun x=>f x^2)) (bad : ¬LocalAffine f)
variable (even : ∀q bit,Even (∑v,P.signedCount (rows D schedule v) q bit))
include masks square bad even in
theorem nonaffine : ¬Affine (fun z=>∏v : Fin (k+1),f (word (rows D schedule v) z)):=by
  obtain ⟨a,z,i,j,l,failed⟩:=NoXLocalAffineCubeWitness.witness D square bad
  have coreBad : ¬Affine (core D a):=by
    intro good
    exact failed (thirdTrivial_of_affine
      (fun x=>(NoXLocalRankOneCriterion.twist_support f _ _).mpr (D.supported x)) good
      z (basis i) (basis j) (basis l))
  have productBad:=C.multiply_affine_core (core D a) (multiplier D schedule a) coreBad
    (multiplier_affine D schedule masks a) (multiplier_full D schedule a)
  intro good
  have phase:=(NoXGeneralEvenBundlePhase.affine (rows D schedule) even (C.codeSeven a)).precompose
    C.codeSeven C.codeSeven_affine
  have pulled:=phase.mul (good.precompose C.codeSeven C.codeSeven_affine)
  apply productBad
  simpa only [value] using pulled

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralLocalRankThreeBundle
end
