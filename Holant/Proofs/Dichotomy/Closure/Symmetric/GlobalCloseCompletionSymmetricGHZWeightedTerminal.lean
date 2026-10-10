import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZWeighted
import Holant.Proofs.Dichotomy.Closure.Ambient.GlobalCloseCompletionAmbientTrace

/-! An actual nonzero weighted equality-three and a retained nonsingular
trace-zero row close the complete ordinary source. Both finite-field source
steps and the final hardness programme return to the unchanged original G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZWeightedTerminal
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
namespace W
export GlobalCloseCompletionSymmetricGHZWeighted (data old_included)
end W
namespace U
export GlobalCloseCompletionUnaryDescentSource (ambient)
end U
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph (symmetric)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {arity b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=arity)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (N : Macro H 3) (a d : L) (ha : a≠0) (hd : d≠0)
variable (form : N.network.denote=C.symmetric a 0 0 d)

include F back N a d ha hd form in
theorem classified (Q : InvertibleKernel)
    (member : (⟨2,kernelSignature Q.matrix⟩ : AnySignature AlgebraicComplex)∈U.ambient L H)
    (trace : Matrix.trace (Matrix.of Q.matrix)=0) :
    Tract (U.ambient L H) ∨ NoXWeightedAntiResourcesOriginal.Hard G := by
  let src:=W.data G L F H N a d ha hd form back
  have included : U.ambient L H⊆GenericOrdinarySource.family G src:=
    W.old_included G L F H N a d ha hd form back
  have determinant : (Matrix.of Q.matrix).det≠0 := by
    rw [Holant.Complexity.BinaryInterpolation.det_entries]
    exact Holant.Tractable.SymmetricBinaryPullback.determinant_ne_zero Q
  rcases GlobalCloseCompletionAmbientTrace.of_matrix G src (Matrix.of Q.matrix)
    (included member) trace determinant with positive|hard
  · exact Or.inl (positive.mono_family included)
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZWeightedTerminal
end
