import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryPinAntiLift
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorPins

/-! An actual ordinary Eq4 graph and any old q4 with two live mixed entries
close the complete old ordinary family through the genuine weighted-anti
consumer, including its LocalAffine-sensitive eighth-root case. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryAnchorPinAnti
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace I
export GlobalCloseCompletionOrdinaryAnchorInput (Input mapped)
end I
namespace P
export GlobalCloseCompletionOrdinaryAnchorPins (data old_included)
end P
namespace L
export PaperControlled.C2OrdinaryPinAntiLift (Input classified)
end L
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val)) (D : I.Input G)
local instance : Algebra ℚ D.K := D.K.algebra'
variable (N : Macro D.H 4) (c d : D.K) (hc : c≠0) (hd : d≠0)
variable (pinned : ∀x : Fin 2→Bool,N.network.denote ![false,true,x 0,x 1]=NoXWeightedAntiSigned.anti c d x)

def input : L.Input G (P.data G D) where
  network := N.network.map D.K.subtype
  uses := by
    intro v
    apply P.old_included G D
    exact ⟨N.labels.vertex v,congrArg (RingHomRealization.mapAny D.K.subtype) (N.exact v)⟩
  ordinary := by
    intro e
    funext u v
    change D.K.subtype (N.network.edge e u v)=Signature.equality u v
    rw [N.edges]
    cases u <;> cases v <;> rfl
  c := (c : AlgebraicComplex)
  d := (d : AlgebraicComplex)
  cNonzero := by intro zero; exact hc (Subtype.ext zero)
  dNonzero := by intro zero; exact hd (Subtype.ext zero)
  pinned := by
    intro x
    rw [Network.denote_map,pinned]
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp [NoXWeightedAntiSigned.anti,h0,h1] <;> rfl

include N c d hc hd pinned in
theorem classified : Tract (UniversalPairReduction.FiniteFamily.family (I.mapped G D)) ∨
    PaperControlledHardness.Original G := by
  rcases L.classified G (P.data G D) (input G D N c d hc hd pinned) with tract|hard
  · exact Or.inl (tract.mono_family (P.old_included G D))
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryAnchorPinAnti
end
