import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicSixResource
import Holant.Proofs.Algorithms.RingHomDescent

/-! Descend the genuine two-copy six-port source to the unchanged original
field; recover its nonzero scalar at the all-zero output coefficient. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicSixActual
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace RH
export RingHomRealization (mapSignature mapFamily)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type*} [Field K] [NumberField K]
def even4 : Signature K 4 := fun x=>if (((x 0).xor (x 1)).xor (x 2)).xor (x 3) then 0 else 1

theorem current_actual (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (phi : K→+*ℂ)
    (cyclic : IsCyclic (completeGroup (RH.mapFamily phi F)
      (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)))
    (f : Signature K 6) (retained : (⟨6,f⟩ : AnySignature K)∈F)
    (prime : Prime (⟨6,f⟩ : AnySignature K))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    ∃c : K,c≠0 ∧ Gadget.Realizes F .disequality (c • even4) := by
  have group := actualTransfers_projectiveMatrixGroup _ (actualTransfers_nonempty _)
    (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)
  have span := GlobalCloseCompletionCyclicHigherField.actual_span _
    (ClosureFieldBridgeGroups.mappedTorsion phi F torsion)
    (GlobalCloseCompletionCyclicHigherDeck.identity_map phi hI) cyclic
  have ident : (⟨2,Holant.ReedMuller.WeightTwoIntegration.literalI⟩ : AnySignature ℂ)∈RH.mapFamily phi F :=
    GlobalCloseCompletionCyclicHigherDeck.identity_map phi hI
  have mem : (⟨6,RH.mapSignature phi f⟩ : AnySignature ℂ)∈RH.mapFamily phi F := ⟨_,retained,rfl⟩
  have actual := GlobalCloseCompletionCyclicSixResource.realizes _ group span
    (RH.mapSignature phi f) ((prime_mapSignature_iff phi _).mpr prime)
    (GlobalCloseCompletionCyclicHigherDeck.current_deck F torsion hI phi f stable)
    (RH.mapFamily phi F) ident mem
  obtain ⟨d,hd,N,uses,native,equation⟩ := actual
  let M := RingHomDescent.descendNetwork phi N uses
  have hm : RH.mapSignature phi M.tensor=d • Holant.ReedMuller.WeightTwoIntegration.even4 :=
    (RingHomDescent.descend_tensor phi N uses).trans equation
  let c : K := M.tensor (fun _=>false)
  have hcmap : phi c=d := by
    have h:=congrFun hm (fun _=>false)
    simpa only [RH.mapSignature,Pi.smul_apply,smul_eq_mul,
      Holant.ReedMuller.WeightTwoIntegration.even4,Bool.false_xor,Bool.false_eq_true,ite_false,mul_one] using h
  have hc : c≠0 := by intro h;apply hd;rw [←hcmap,h,map_zero]
  refine ⟨c,hc,M,RingHomDescent.descend_labels phi N uses,native,?_⟩
  funext x
  apply phi.injective
  have h:=congrFun hm x
  change phi (M.tensor x)=phi ((c • even4) x)
  rw [show phi ((c • even4) x)=d*Holant.ReedMuller.WeightTwoIntegration.even4 x by
    simp only [Pi.smul_apply,smul_eq_mul,map_mul,hcmap,even4,Holant.ReedMuller.WeightTwoIntegration.even4]
    split <;> simp]
  exact h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicSixActual
end
