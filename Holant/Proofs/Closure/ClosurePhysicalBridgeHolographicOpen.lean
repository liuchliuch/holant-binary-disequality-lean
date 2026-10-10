import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicClosed
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra

/-! Genuine inverse holographic transport for an actual OPEN current-family
row graph and supplied actual basis. Literal inverse-action source labels and
native edges are derived, the exact shape is retained, and the full free-port
output action is proved before original-field descent/physical compilation.
This does not select a marked basis or assume any new boundary gadget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.FinitePGL2.Stabilization

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (B : InvertibleKernel) {n : ℕ} (N : Network AlgebraicComplex n)
variable (labels : ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex) ∈
  familyAction B (RH.mapFamily (algebraicEmbedding G) P.family))
variable (edges : ∀ e, N.edge e = Kernel.pullback Signature.disequality B.inverse)

/-- Actual basis inverse at every ordered vertex port and corresponding
forward pullback at every ordered internal edge occurrence. -/
def restoredOpen : Network AlgebraicComplex n :=
  OpenHolographic.transform N B.matrix B.inverse

include labels in
theorem restoredOpen_labels (v : Fin N.shape.vertices) :
    (⟨(restoredOpen B N).shape.arity v,(restoredOpen B N).vertex v⟩ : AnySignature AlgebraicComplex) ∈
      RH.mapFamily (algebraicEmbedding G) P.family :=
  inverse_family_label B _ (N.vertex v) (labels v)

include edges in
theorem restoredOpen_native (e : Fin N.shape.edges) :
    (restoredOpen B N).edge e = Signature.disequality := by
  change Kernel.pullback (N.edge e) B.matrix = Signature.disequality
  rw [edges e]
  exact pullback_inverse _ _ _ B.inverse_matrix

/-- OPEN graphs keep the inverse action on all free ordered ports. -/
theorem restoredOpen_denote : (restoredOpen B N).denote = B.symm.action N.denote :=
  OpenHolographic.denote_transform N B.matrix B.inverse B.matrix_inverse

/-- The entire graph transforms back, not only its output table. -/
theorem restoredOpen_forward :
    OpenHolographic.transform (restoredOpen B N) B.inverse B.matrix = N := by
  cases N with
  | mk shape vertex edge =>
    unfold restoredOpen OpenHolographic.transform
    congr 1
    · funext v
      exact B.action_symm_action (vertex v)
    · funext e
      exact pullback_inverse (edge e) B.matrix B.inverse B.matrix_inverse

structure HolographicOpenAccess where
  restored : Network AlgebraicComplex n
  restoredIdentity : restored = restoredOpen B N
  sameShape : restored.shape = N.shape
  labels : ∀ v, (⟨restored.shape.arity v,restored.vertex v⟩ : AnySignature AlgebraicComplex) ∈
    RH.mapFamily (algebraicEmbedding G) P.family
  native : ∀ e, restored.edge e = Signature.disequality
  boundaryAction : restored.denote = B.symm.action N.denote
  forwardGraph : OpenHolographic.transform restored B.inverse B.matrix = N
  access : NetworkGraphAccess G P (algebraicEmbedding G) restored labels
  accessIdentity : access = fromNetwork G P (algebraicEmbedding G) restored labels native
  mappedOutput : RH.mapSignature (algebraicEmbedding G) access.output = B.symm.action N.denote
  forwardOutput : B.action (RH.mapSignature (algebraicEmbedding G) access.output) = N.denote

/-- Known basis, actual changed labels and EXACT changed edge are inputs;
restored mapped-P availability and both original-G physical programmes are
conclusions. The charged table maps to the inverse-transformed open output,
not falsely to the untransformed row output when n>0. -/
def fromHolographicOpen : HolographicOpenAccess G P B N := by
  let D := restoredOpen B N
  let d := fromNetwork G P (algebraicEmbedding G) D
    (restoredOpen_labels G P B N labels) (restoredOpen_native B N edges)
  have hm : RH.mapSignature (algebraicEmbedding G) d.output = B.symm.action N.denote :=
    d.mappedOutput.trans (restoredOpen_denote B N)
  exact ⟨D,rfl,rfl,restoredOpen_labels G P B N labels,restoredOpen_native B N edges,
    restoredOpen_denote B N,restoredOpen_forward B N,d,rfl,hm,
    (congrArg B.action hm).trans (B.action_symm_action N.denote)⟩

abbrev HolographicOpenAccess.output (d : HolographicOpenAccess G P B N) := d.access.output
abbrev HolographicOpenAccess.toOriginal (d : HolographicOpenAccess G P B N) := d.access.toOriginal
abbrev HolographicOpenAccess.fromOriginal (d : HolographicOpenAccess G P B N) := d.access.fromOriginal

/-- Exact ordinary source graph maps and forward-transports to the ORIGINAL
row graph, including all scalar-only components and incidence geometry. -/
theorem HolographicOpenAccess.sourceForward (d : HolographicOpenAccess G P B N) :
    OpenHolographic.transform (d.access.source.map (algebraicEmbedding G)) B.inverse B.matrix = N := by
  rw [d.access.mappedNetwork]
  exact d.forwardGraph
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge
