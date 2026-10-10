import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryHadamard
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryPairTerminal
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource

/-! The dense same-sign paired q4 arm closes the whole old ordinary family.
The formal Hadamard frame is a genuine same-field source, its retained Z
makes X, and the symmetric-pair outcome installs real Eq4 or counts Ising. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryHadamardTerminal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace H
export GlobalCloseCompletionC2OrdinaryHadamard
  (unary norm_unary chartTable chartMacro xOutput signatures arity oldMacro source same_sign_form)
end H
namespace X
export GlobalCloseCompletionOrdinaryXAdjoin (old old_literal xLabel x_literal)
end X
namespace P
export PaperControlled.C2OrdinaryPairTerminal (Input classified family)
end P
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (F : FixedField K degree) (S : (i : Fin r)→Signature K (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F S).evaluate F) (OriginalForestSource.value G))
variable (N : Macro S 4) (z : Fin r)
variable (zLiteral : (⟨b z.val,S z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)
variable (A C : K) (hA : A≠0) (hC : C≠0) (form : N.network.denote=T.normal A A C C)

def input : P.Input G where
  K := K
  degree := degree
  F := F
  count := r+1
  b := H.arity S z zLiteral
  H := H.signatures F S z zLiteral
  graph := H.oldMacro F S z zLiteral (H.chartMacro S N)
  xLabel := X.xLabel (H.chartTable S)
  xLiteral := X.x_literal F (H.chartTable S) (H.xOutput S z zLiteral)
  a := (2:K)^N.network.shape.edges*(4*(A+C))
  d := (2:K)^N.network.shape.edges*(4*(A-C))
  form := H.same_sign_form F S z zLiteral N A C form
  determinant := by
    have hn : (2:K)^N.network.shape.edges≠0 := pow_ne_zero _ (by norm_num)
    have live : ((2:K)^N.network.shape.edges)^2*64*A*C≠0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hn) (by norm_num)) hA) hC
    intro eqn
    apply live
    linear_combination eqn
  toOriginal := Programme.compose (H.source F S z zLiteral) back

include back N z zLiteral hA hC form in
theorem classified : Tract (GlobalCloseCompletionUnaryDescentSource.ambient K S) ∨
    PaperControlledHardness.Hard
      (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
      (OriginalForestSource.value G) := by
  rcases P.classified G (input G K F S back N z zLiteral A C hA hC form) with tract|hard
  · left
    have included : GlobalCloseCompletionUnaryEndpointSource.chartedFamily K S H.unary⊆
        P.family G (input G K F S back N z zLiteral A C hA hC form) := by
      rintro f ⟨i,rfl⟩
      refine ⟨X.old (H.chartTable S) i,?_⟩
      exact congrArg (RingHomRealization.mapAny K.subtype)
        (X.old_literal F (H.chartTable S) (H.xOutput S z zLiteral) i)
    have charted := tract.mono_family included
    have hn : GeneralOddNonisotropicFrame.norm (H.unary (K:=K))≠0 := by rw [H.norm_unary]; norm_num
    rw [GlobalCloseCompletionUnaryDescentSource.charted_exact K S H.unary hn] at charted
    exact (GlobalCloseCompletionUnaryDescentSource.tract_frame _ _ _).mpr charted
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryHadamardTerminal
end
