import Holant.Proofs.Closure.ClosureSourceRowsC2Group
import Holant.ReedMuller.FlatNetwork.Primitives
import Holant.ReedMuller.AffineRadon.PhysicalBridge
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatNonzero

/-! Every genuinely retained binary prime in the literal current C2 branch
is Flat in the original coordinates. The actual complete group supplies its
exact original-field scalar; no binary membership backend is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2BinaryFlat
open Holant Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.AffineRadon
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type*} [Field K] [NumberField K]

theorem literal (phi : K→+*ℂ) (p : Bool) :
    Flat (RingHomRealization.mapSignature phi
      (binarySignature (ClosureSourceRows.originalC2Binary (L:=K) p))) := by
  have h := parityKernel_flat (if p then 1 else 0)
  convert h using 1
  funext x
  cases p <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [RingHomRealization.mapSignature,binarySignature,ClosureSourceRows.originalC2Binary,
      parityKernel,boolEquiv,X,Signature.disequality,Matrix.one_apply,h0,h1]

theorem retained (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion)=2)
    (phi : K→+*ℂ) (f : Signature K 2)
    (mem : (⟨2,f⟩ : AnySignature K)∈F) (prime : Prime (⟨2,f⟩ : AnySignature K)) :
    Flat (RingHomRealization.mapSignature phi f) := by
  obtain ⟨p,c,hc,equation⟩ := ClosureSourceRows.c2_actual_binary F torsion hI cardTwo
    (binaryMatrix f) (retained_binary_prime_actual F f mem prime)
  have h := flat_nonzero_smul _ (literal phi p) (phi c) (fun hz => hc (phi.injective (hz.trans (map_zero phi).symm)))
  convert h using 1
  funext x
  have e := congrArg (fun B => B (x 0) (x 1)) equation
  have hx : ![x 0,x 1]=x := by funext i;fin_cases i <;> rfl
  change phi (f x)=phi c * phi (ClosureSourceRows.originalC2Binary p (x 0) (x 1))
  rw [←map_mul]
  apply congrArg phi
  simpa only [binaryMatrix,hx,Matrix.smul_apply,smul_eq_mul] using e

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2BinaryFlat
end
