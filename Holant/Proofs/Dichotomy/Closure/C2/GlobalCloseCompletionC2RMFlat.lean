import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2ReedMuller
import Holant.ReedMuller.FlatNetwork.Relabel

/-! The exact current RM8 coefficient theorem gives the actual phase-free
self-dual flat class, not only Affine. Its original shift, scalar and port
permutation are the witnesses of the Flat definition. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RMFlat
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CoefficientAtlas
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem of_coefficients (f : Signature ℂ 8) (e : Equiv.Perm (Fin 8)) (a : BinaryVector 8)
    (c : ℂ) (hc : c≠0)
    (equation : ∀x,f x=if (fun p=>boolEquiv (x (e p)))+a∈code then c else 0) : Flat f := by
  have hflat : Flat (flatSignature (Units.mk0 c hc) a code) := ⟨Units.mk0 c hc,a,code,code_selfDual,rfl⟩
  have h := flat_reindex e _ hflat
  convert h using 1
  funext x
  rw [equation]
  have words : (fun p=>bit (x (e p))-a p)=(fun p=>boolEquiv (x (e p)))+a := by
    funext p
    change boolEquiv (x (e p))-a p=boolEquiv (x (e p))+a p
    have hn : ∀z : ZMod 2,-z=z := by decide
    rw [sub_eq_add_neg,hn]
  simp only [Tensor.reindex,flatSignature,words,Units.val_mk0]

variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F)
variable (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion)=2)
variable (phi : K→+*ℂ)
include torsion hI cardTwo in
theorem current_flat (f : Signature K 8) (prime : Prime (⟨8,f⟩ : AnySignature K))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    Flat (RingHomRealization.mapSignature phi f) := by
  obtain ⟨e,c,a,hc,equation⟩ := GlobalCloseCompletionC2ReedMuller.current_prime_exact_code F torsion hI cardTwo phi f prime stable
  exact of_coefficients _ e a c hc equation

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2RMFlat
end
