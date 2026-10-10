import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryDenseOrbit
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinarySeparatedTerminal
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryHadamardTerminal
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryOppositeTerminal

/-! Complete dense ordinary complementary-even q4 consumer. Every case is
selected from the actual coefficients; all source dictionaries, fixed fields,
port orders, and final original-G reductions are preserved. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryDenseTerminal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
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
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
variable (back : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (N : Macro H 4) (A B C D : K) (hA : A≠0) (hB : B≠0) (hC : C≠0) (hD : D≠0)
variable (form : N.network.denote=T.normal A B C D)
variable (z : Fin r) (zLiteral : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

include back form hA hB hC hD zLiteral in
theorem classified : Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H) ∨
    OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G := by
  rcases GlobalCloseCompletionC2OrdinaryDenseOrbit.split_dense H z zLiteral N A B C D hA hB hC hD form with
    ⟨Q,a0,b0,c0,d0,ha,hb,hc,hd,form,sep⟩|⟨Q,A0,C0,ha,hc,form⟩
  · let input : GlobalCloseCompletionC2OrdinarySeparated.Input G := {
      K := K
      degree := degree
      F := F
      count := r
      b := b
      H := H
      graph := Q.network
      labels := Q.labels
      exact := Q.exact
      ordinary := Q.edges
      zLabel := z
      z := 1
      zNonzero := one_ne_zero
      zLiteral := by
        exact zLiteral.trans (congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K))
          (by funext x; change T.Z (x 0) (x 1)=1*T.Z (x 0) (x 1); rw [one_mul]))
      a := a0
      b0 := b0
      c := c0
      d := d0
      form := form
      separated := sep
      toOriginal := back }
    exact GlobalCloseCompletionC2OrdinarySeparatedTerminal.classified G input ha hc hd
  · rcases form with same|opposite
    · exact GlobalCloseCompletionC2OrdinaryHadamardTerminal.classified G K F H back Q z zLiteral A0 C0 ha hc same
    · exact GlobalCloseCompletionC2OrdinaryOppositeTerminal.classified G K F H back Q A0 C0 ha hc opposite z zLiteral

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryDenseTerminal
end
