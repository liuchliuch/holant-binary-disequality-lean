import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsPins

/-! A pure pinning is flattened into the unchanged original row. Both signed
multiplicities, and the exact coefficient on opposite assignments, survive. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXSeparateSignedPins
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export OrdinaryNegativeSignedRowsPins (signedCompose word_compose sum_pure)
export OrdinaryNegativeSparseMinimalRank (PurePins)
end P
namespace S
export NoXSeparateSignedSource (resource ambient_value)
export NoXSeparateSignedProjection (signedCount)
end S
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {N n m : ℕ}
section Counts
variable (pins : Fin N→Bool ⊕ Fin n) (pure : P.PurePins pins)
variable (ps : Fin n→Port m)

include pure in
theorem signedCount_compose (j : Fin m) (bit : Bool) :
    S.signedCount (P.signedCompose pins ps) j bit=S.signedCount ps j bit := by
  unfold S.signedCount
  calc
    _=∑i : Fin N,Sum.elim (fun _=>0) (fun q=>if ps q=.inr (j,bit) then 1 else 0) (pins i) := by
      apply Finset.sum_congr rfl
      intro i _
      cases h : pins i <;> simp [P.signedCompose,h]
    _=_ := P.sum_pure pins pure _

end Counts

variable (ps : Fin n→Port m)
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (pins : Fin (b j.val)→Bool ⊕ Fin n) (pure : P.PurePins pins)
variable (odd : ∀q bit,Odd (S.signedCount ps q bit))

def resource := S.resource H j p0 p1 h0 h1 (P.signedCompose pins ps)
  (by intro q bit;rw [signedCount_compose pins pure];exact odd q bit)

theorem ambient_value (z : Fin m→Bool) :
    (resource ps H j p0 p1 h0 h1 pins pure odd).ambient H (Fin.addCases z (fun i=>!(z i)))=
      (H j (T.substitute pins (word ps z)) : AlgebraicComplex) := by
  rw [resource,S.ambient_value,P.word_compose]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXSeparateSignedPins
end
