import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesNormalize
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCapGraph
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZEquality

/-! Any genuine nonzero weighted equality-three supplies an ordinary Eq4
source. Its two-copy graph has a diagonal paired matrix; the exact inverse
of its binary loop normalizes both weights, retaining the complete dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZWeighted
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
namespace E
export GlobalCloseCompletionSymmetricGHZEquality (join join_value)
end E
namespace C
export GlobalCloseCompletionSymmetricGHZCapGraph (symmetric)
end C
namespace P
export GlobalCloseCompletionPairedSeriesCore (row identity smul)
export GlobalCloseCompletionPairedSeriesNormalize (extension normalized value loop_matrix)
end P
namespace D
export OrdinaryTargetInterpolationDiagonal (diagonal)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {r degree : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin r)→Signature K (arity i.val)) (F : FixedField K degree)
variable (N : Macro H 3) (a d : K) (ha : a≠0) (hd : d≠0)
variable (form : N.network.denote=C.symmetric a 0 0 d)

include form in
theorem joined : (E.join H N).network.denote=P.row (D.diagonal (a^2) (d^2)) := by
  funext x
  rw [E.join_value,form]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [C.symmetric,P.row,D.diagonal,h0,h1,h2,h3,pow_two]

def extension := P.extension H F (E.join H N) (D.diagonal (a^2) (d^2)) (joined H N a d form)
  (by exact pow_ne_zero _ ha) (by exact pow_ne_zero _ hd)
abbrev newArity := (extension H F N a d ha hd form).b
abbrev table := (extension H F N a d ha hd form).table
def graph : Macro (table H F N a d ha hd form) 4 :=
  P.normalized H F (E.join H N) (D.diagonal (a^2) (d^2)) (joined H N a d form)
    (by exact pow_ne_zero _ ha) (by exact pow_ne_zero _ hd)

theorem graph_value : (graph H F N a d ha hd form).network.denote=
    (extension H F N a d ha hd form).scalar • Holant.EightVertex.ProductAnchor.equalityFour := by
  rw [graph,P.value]
  have inverse := (extension H F N a d ha hd form).right_inverse
  have matrix := P.loop_matrix H (E.join H N) (D.diagonal (a^2) (d^2)) (joined H N a d form)
  change GlobalCloseCompletionSymmetricGHZInverse.matrix H
    (GlobalCloseCompletionPairedSeriesCaps.output (E.join H N).contract)=D.diagonal (a^2) (d^2) at matrix
  rw [matrix] at inverse
  erw [inverse]
  rw [P.smul,P.identity]

section Original
variable {s : ℕ} {b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (b i.val))
local instance : NumberField (OI.K G):=OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L:=L.algebra'
variable (F : FixedField L degree) (S : (i : Fin r)→Signature L (arity i.val))
variable (N : Macro S 3) (a d : L) (ha : a≠0) (hd : d≠0)
variable (form : N.network.denote=C.symmetric a 0 0 d)
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 arity) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=b)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F S).evaluate F) (OriginalForestSource.value G))

def anchor : GlobalCloseCompletionOrdinaryAnchorInput.Input G where
  K:=L
  degree:=degree
  F:=F
  count:=(extension S F N a d ha hd form).count
  b:=newArity S F N a d ha hd form
  H:=table S F N a d ha hd form
  graph:=(graph S F N a d ha hd form).network
  labels:=(graph S F N a d ha hd form).labels
  exact:=(graph S F N a d ha hd form).exact
  ordinary:=(graph S F N a d ha hd form).edges
  scalar:=(extension S F N a d ha hd form).scalar
  nonzero:=(extension S F N a d ha hd form).nonzero
  denote:=graph_value S F N a d ha hd form
  toOriginal:=Programme.compose (extension S F N a d ha hd form).source back

def data : GenericOrdinarySource.Data G:=GlobalCloseCompletionOrdinaryAnchorPins.data G
  (anchor G L F S N a d ha hd form back)

theorem old_included : GlobalCloseCompletionUnaryDescentSource.ambient L S⊆GenericOrdinarySource.family G
    (data G L F S N a d ha hd form back) := by
  intro f member
  apply GlobalCloseCompletionOrdinaryAnchorPins.old_included G (anchor G L F S N a d ha hd form back)
  obtain ⟨i,rfl⟩:=member
  refine ⟨(extension S F N a d ha hd form).old i,?_⟩
  exact congrArg (RingHomRealization.mapAny L.subtype) ((extension S F N a d ha hd form).old_literal i)


end Original
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZWeighted
end
