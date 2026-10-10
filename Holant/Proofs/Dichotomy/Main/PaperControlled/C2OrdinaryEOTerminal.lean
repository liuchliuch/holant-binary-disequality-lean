import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryEOEq4
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryAnchorAnti
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2PairAffine
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource

/-! Sparse ordinary EO q4 consumption: fourth-power agreement has a literal
affine witness, and its failure supplies real Eq4 and full weighted anti.
The complete weighted-anti consumer retains the whole old ordinary family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryEOTerminal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace E
export GlobalCloseCompletionC2OrdinaryEOEq4 (graph graph_denote)
end E
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (symmetric)
end P
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
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
variable (z : Fin r) (zLiteral : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)
variable (N : Macro H 4) (p q : K) (hp : p≠0) (hq : q≠0) (form : N.network.denote=T.normal 0 0 p q)

include form hp in
theorem affine_of_fourth (fourth : p^4=q^4) : Affine (RingHomRealization.mapSignature K.subtype N.network.denote) := by
  have hp' : (p:AlgebraicComplex)≠0 := by intro zero; exact hp (Subtype.ext zero)
  have fourth' : (p:AlgebraicComplex)^4=(q:AlgebraicComplex)^4 := by exact congrArg K.subtype fourth
  have h := EOBinaryPlaneTract.affine_lift (GlobalCloseCompletionC2PairAffine.binary_fourth _ _ hp' fourth')
  convert h using 1
  funext x
  rw [form]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [RingHomRealization.mapSignature,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      EOBinaryPlaneCore.lift,M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3] <;> rfl

include back zLiteral form hp hq in
theorem classified : Affine (RingHomRealization.mapSignature K.subtype N.network.denote) ∨
    Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H) ∨ PaperControlledHardness.Original G := by
  by_cases fourth : p^4=q^4
  · exact Or.inl (affine_of_fourth K H N p q hp form fourth)
  right
  let Q := E.graph H N z zLiteral
  let input : GlobalCloseCompletionOrdinaryAnchorInput.Input G := {
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
    scalar := p^4-q^4
    nonzero := sub_ne_zero.mpr fourth
    denote := E.graph_denote H N z zLiteral p q form
    toOriginal := back }
  exact PaperControlled.C2OrdinaryAnchorAnti.classified G input N 0 0 p q hp hq form

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2OrdinaryEOTerminal
end
