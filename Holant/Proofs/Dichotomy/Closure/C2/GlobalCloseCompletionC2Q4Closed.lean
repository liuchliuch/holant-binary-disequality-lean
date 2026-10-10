import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCertificates.Node100
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCurrent

/-! Kernel-checked complete q4 union, joined to its real ordered I/X deck. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Closed
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace U
export GlobalCloseCompletionC2Q4Union (Safe Accepted node100Covers)
end U
namespace C
export GlobalCloseCompletionC2Q4UnionCurrent (coefficients safe_coefficients)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false

theorem safe_accepted (v : Fin 8→ℂ) (h : U.Safe v) : U.Accepted v := by
  apply U.node100Covers v _ h
  intro row member
  simp [GlobalCloseCompletionC2Q4Union.node100Rows,GlobalCloseCompletionC2SparseInteger.toIRows,
    Holant.Pauli.ExoticKlein.SixPort.IntegerCertificate.mapRows] at member

variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F)
variable (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion)=2)
variable (phi : K→+*ℂ)

include torsion hI cardTwo in
theorem current_accepted (f : Signature K 4)
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    U.Accepted (C.coefficients (RingHomRealization.mapSignature phi f)) := by
  apply safe_accepted
  apply C.safe_coefficients
  · intro x
    exact congrArg phi (GlobalCloseCompletionC2CurrentComplement.current_complement F torsion hI cardTwo f stable x)
  · exact (GlobalCloseCompletionC2SafeSymmetry.current_safe F torsion hI cardTwo f stable).map phi

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Closed
end
