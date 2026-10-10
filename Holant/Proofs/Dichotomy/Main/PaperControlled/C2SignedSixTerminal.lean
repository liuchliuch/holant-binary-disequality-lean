import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSixSquare
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPairEq4
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryAnchorPinAnti
import Holant.Proofs.Dichotomy.Main.PaperControlled.C2OrdinaryThreeTerminal

/-! Genuine signed six-vertex consumption. A two-copy ordinary square either
has three live coefficients, or one of two differently ordered squares gives
actual Eq4. The original signed pinned face supplies the full weighted anti. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2SignedSixTerminal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed square square_signed side side_square other other_square)
end S
namespace E
export GlobalCloseCompletionC2OrdinaryPairEq4 (graph graph_denote)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
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

include back zLiteral in
theorem finish (Q : Macro H 4) (u v : K) (form : Q.network.denote=T.normal u 0 v 0)
    (separated : u^2≠v^2) (N : Macro H 4) (c d : K) (hc : c≠0) (hd : d≠0)
    (pinned : ∀x : Fin 2→Bool,N.network.denote ![false,true,x 0,x 1]=NoXWeightedAntiSigned.anti c d x) :
    Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H) ∨ PaperControlledHardness.Original G := by
  let W := E.graph H Q z zLiteral
  let input : GlobalCloseCompletionOrdinaryAnchorInput.Input G := {
    K := K
    degree := degree
    F := F
    count := r
    b := b
    H := H
    graph := W.network
    labels := W.labels
    exact := W.exact
    ordinary := W.edges
    scalar := u^2-v^2
    nonzero := sub_ne_zero.mpr separated
    denote := E.graph_denote H Q z zLiteral u v form
    toOriginal := back }
  exact PaperControlled.C2OrdinaryAnchorPinAnti.classified G input N c d hc hd pinned

include back zLiteral in
theorem live (N : Macro H 4) (B C D : K) (hB : B≠0) (hC : C≠0) (hD : D≠0)
    (form : N.network.denote=S.signed B C D) :
    Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H) ∨ PaperControlledHardness.Original G := by
  by_cases hs : C^2+D^2≠0
  · exact PaperControlled.C2OrdinaryThreeTerminal.endpoint_live G K F H back z zLiteral
      (S.square H N) (-B^2) 0 (C^2+D^2) (2*C*D) (neg_ne_zero.mpr (pow_ne_zero _ hB))
      hs (mul_ne_zero (mul_ne_zero (by norm_num) hC) hD) (S.square_signed H N B C D form)
  have sum : C^2+D^2=0 := not_not.mp hs
  have pinned : ∀x : Fin 2→Bool,N.network.denote ![false,true,x 0,x 1]=NoXWeightedAntiSigned.anti C D x := by
    intro x
    rw [form]
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [S.signed,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,NoXWeightedAntiSigned.anti,h0,h1]
  by_cases first : (C^2)^2≠(B^2+D^2)^2
  · exact finish G K F H back z zLiteral (S.square H (S.side H N)) (C^2) (B^2+D^2)
      (S.side_square H N B C D form) first N C D hC hD pinned
  have second : (D^2)^2≠(B^2+C^2)^2 := by
    intro h2
    have h1 := not_not.mp first
    have d2 : D^2= -C^2 := by linear_combination sum
    rw [d2] at h1 h2
    have nonzero : (4:K)*B^2*C^2≠0 := mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hB)) (pow_ne_zero _ hC)
    apply nonzero
    linear_combination h1-h2
  exact finish G K F H back z zLiteral (S.square H (S.other H N)) (D^2) (B^2+C^2)
    (S.other_square H N B C D form) second N C D hC hD pinned

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.C2SignedSixTerminal
end
