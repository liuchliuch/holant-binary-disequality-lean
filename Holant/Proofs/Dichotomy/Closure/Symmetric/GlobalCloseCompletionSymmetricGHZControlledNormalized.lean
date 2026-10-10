import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZWeighted
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCommonBasis
import Holant.Proofs.Dichotomy.Main.PaperControlledOrdinary

/-! Final whole-family consumer for the constructed normalized GHZ source.
The actual weighted ternary supplies Eq4 and both pins; the generic ordinary
terminal retains the controlled counted-verifier programme. The retained Gram row restores one
common basis for the entire original family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZControlledNormalized
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization OrdinaryNegativeCubicGadgets
namespace W
export GlobalCloseCompletionSymmetricGHZWeighted (data old_included)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K:=K.algebra'
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (N : Macro H 3) (p q : K) (hp : p≠0) (hq : q≠0)
variable (weighted : N.network.denote=GlobalCloseCompletionSymmetricGHZCapGraph.symmetric p 0 0 q)
variable (original : SignatureFamily AlgebraicComplex) (finite : original.Finite) (R : InvertibleKernel)
variable (included : familyAction R.symm original⊆GlobalCloseCompletionUnaryDescentSource.ambient K H)
variable (gram : (⟨2,kernelSignature (Kernel.pullback Signature.equality R.matrix)⟩ : AnySignature AlgebraicComplex)∈
    GlobalCloseCompletionUnaryDescentSource.ambient K H)

include back hp hq weighted finite included gram in
theorem classified : Tract original ∨ PaperControlledHardness.Original G := by
  let src:=W.data G K F H N p q hp hq weighted back
  have old:=W.old_included G K F H N p q hp hq weighted back
  rcases PaperControlledOrdinary.classified G src with positive|hard
  · left
    exact GlobalCloseCompletionSymmetricGHZCommonBasis.tract original (GenericOrdinarySource.family G src)
      finite R (fun f member=>old (included member)) (old gram) (GenericOrdinarySource.family_eq4 G src) positive
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZControlledNormalized
end
