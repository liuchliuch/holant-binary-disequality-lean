import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SixPortCoordinates
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2MatchingLines

/-! The actual original-field C2 raw deck supplies every input condition of
the literal finite six-port checker, retaining zeros and all thirty ordered
I/X pair contractions. No finite-card classifier is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SixPortCurrent
open Holant Holant.Tractable Holant.Algebraic Holant.OpenNetworkComposition
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureSourceRows
open Holant.Pauli.ExoticKlein.SixPort
open IntegerCertificate LinearCertificate
open GlobalCloseCompletionC2SixPortProblem GlobalCloseCompletionC2SixPortCoordinates
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false
variable {L : Type*} [Field L]

private theorem map_c2 (phi : L →+* ℂ) (p a b : Bool) :
    phi (originalC2Binary p a b) = originalC2Binary p a b := by
  cases p <;> cases a <;> cases b <;>
    simp [originalC2Binary,X,Signature.disequality]

theorem map_contract (phi : L →+* ℂ) {m : ℕ} (f : Signature L (m+2))
    (e : Equiv.Perm (Fin (m+2))) (p : Bool) :
    RingHomRealization.mapSignature phi
      (Signature.contract (originalC2Binary p) (Tensor.reindex e.symm f)) =
    Signature.contract (originalC2Binary p)
      (Tensor.reindex e.symm (RingHomRealization.mapSignature phi f)) := by
  funext w
  simp only [RingHomRealization.mapSignature,Signature.contract,Tensor.reindex,
    map_sum,map_mul,map_c2]

private theorem mapped_line (j : Fin 12) (w : Fin 16) :
    gaussianToComplex (integerToGaussian (line j w)) =
      if w ∈ cardSupport j then 1 else 0 := by
  unfold line
  split_ifs <;> simp only [map_one,map_zero]

variable [NumberField L]
variable (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion) = 2)
include torsion hI cardTwo

/-- Every literal checker card is derived from the same actual stable C2
raw deck and the same original tensor. -/
theorem current_safeCards (phi : L →+* ℂ) (f : Signature L 6)
    (stable : ∀ g ∈ rawDeck F torsion f, MatchingOrZero (actualTransfers F) g) :
    GlobalCloseCompletionC2SixPortProblem.problem.toProblem.SafeCards (coefficients (RingHomRealization.mapSignature phi f)) := by
  intro c
  have matching := DeckContraction.orderedClosure_matching F torsion hI f stable
    (order c) (originalC2Binary (phase c))
    (GlobalCloseCompletionC2CurrentComplement.kernel_member F torsion hI (phase c))
  obtain ⟨j,k,equation⟩ := GlobalCloseCompletionC2MatchingLines.matching_four_line
    F torsion hI cardTwo _ matching
  refine ⟨j,phi k,?_⟩
  intro w
  change evaluate (IntegerCertificate.mapRow (GlobalCloseCompletionC2SixPortProblem.card c w))
    (coefficients (RingHomRealization.mapSignature phi f)) =
      phi k * gaussianToComplex (integerToGaussian (line j w))
  rw [card_contract,mapped_line,←map_contract]
  change phi (Signature.contract (originalC2Binary (phase c)) (Tensor.reindex (order c).symm f)
    ((wordEquiv 4).symm w)) = _
  rw [equation w,map_mul]
  by_cases h : w ∈ cardSupport j <;> simp [h]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2SixPortCurrent
end
