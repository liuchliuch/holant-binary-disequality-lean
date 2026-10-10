import Holant.Proofs.Dichotomy.General.GenericOrdinarySource
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Proofs.Algorithms.KSourceTransport

/-! A finite ordinary table and its actual scalar-Eq4 graph yield a genuine
native finite-table anchor by the fixed source-K change of coordinates.
The original fixed field, literal graph labelling and final oracle programme
remain explicit. No changed-coordinate Palette is fabricated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOrdinaryAnchorInput
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Complexity.FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))

structure Input : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K := K.algebra'; FixedField K degree
  count : ℕ
  b : ℕ→ℕ
  H : (i : Fin count)→Signature K (b i.val)
  graph : Network K 4
  labels : Labelling graph.shape count 1 b
  exact : LabelledNetwork.Exact H graph labels
  ordinary : ∀e,graph.edge e=Signature.equality
  scalar : K
  nonzero : scalar≠0
  denote : graph.denote=fun x=>scalar*Holant.EightVertex.ProductAnchor.equalityFour x
  toOriginal : letI : Algebra ℚ K := K.algebra'; LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G)

variable (D : Input G)
local instance : Algebra ℚ D.K := D.K.algebra'
def mapped (i : Fin D.count) : Signature AlgebraicComplex (D.b i.val) :=
  RingHomRealization.mapSignature D.K.subtype (D.H i)
abbrev native := KSourceTransport.nativeSignatures (mapped G D)
def mappedGraph : Network AlgebraicComplex 4 := D.graph.map D.K.subtype
def nativeGraph : Network AlgebraicComplex 4 := OpenHolographic.transform
  (mappedGraph G D) sourceKBasis.matrix sourceKBasis.inverse

theorem mappedGraph_labels : ∀v,(⟨(mappedGraph G D).shape.arity v,(mappedGraph G D).vertex v⟩ :
    AnySignature AlgebraicComplex)∈UniversalPairReduction.FiniteFamily.family (mapped G D) := by
  intro v
  refine ⟨D.labels.vertex v,?_⟩
  exact congrArg (RingHomRealization.mapAny D.K.subtype) (D.exact v)

theorem nativeGraph_labels : ∀v,(⟨(nativeGraph G D).shape.arity v,(nativeGraph G D).vertex v⟩ :
    AnySignature AlgebraicComplex)∈UniversalPairReduction.FiniteFamily.family (native G D) := by
  intro v
  obtain ⟨i,hi⟩ := mappedGraph_labels G D v
  exact ⟨i,congrArg (fun f : AnySignature AlgebraicComplex=>
    (⟨f.1,sourceKBasis.symm.action f.2⟩ : AnySignature AlgebraicComplex)) hi⟩

theorem nativeGraph_edges : ∀e,(nativeGraph G D).edge e=Signature.disequality := by
  intro e
  change Kernel.pullback (fun b c=>D.K.subtype (D.graph.edge e b c)) sourceKBasis.matrix=_
  rw [D.ordinary]
  have equality : (fun b c=>D.K.subtype (Signature.equality b c))=(Signature.equality : Kernel AlgebraicComplex) := by
    funext b c
    cases b <;> cases c <;> simp [Signature.equality]
  rw [equality,sourceKBasis_pullback]

theorem mappedGraph_denote : (mappedGraph G D).denote=
    fun x=>(D.scalar : AlgebraicComplex)*Holant.EightVertex.ProductAnchor.equalityFour x := by
  funext x
  rw [mappedGraph,Network.denote_map,D.denote,map_mul]
  congr 1
  simp [Holant.EightVertex.ProductAnchor.equalityFour,apply_ite]

theorem nativeGraph_denote : (nativeGraph G D).denote=
    sourceKBasis.symm.action (fun x=>(D.scalar : AlgebraicComplex)*Holant.EightVertex.ProductAnchor.equalityFour x) := by
  rw [nativeGraph,OpenHolographic.denote_transform _ _ _ sourceKBasis.matrix_inverse,mappedGraph_denote]
  rfl

theorem nativeGraph_actual : Gadget.Realizes (UniversalPairReduction.FiniteFamily.family (native G D))
    .disequality (nativeGraph G D).denote :=
  Gadget.realizes_network (nativeGraph G D) _ .disequality (nativeGraph_labels G D) (nativeGraph_edges G D)

theorem inverse_edge : Kernel.pullback Signature.disequality sourceKBasis.inverse=Signature.equality := by
  rw [←sourceKBasis_pullback,←pullback_mul,sourceKBasis.matrix_inverse]
  simp [Kernel.pullback,Kernel.transpose,Kernel.mul_apply,Signature.equality]

def anchor : QuaternaryEqualityTerminal.AnchorStep (UniversalPairReduction.FiniteFamily.family (native G D)) where
  signature := (nativeGraph G D).denote
  basis := sourceKBasis
  edgeScale := 1
  vertexScale := (D.scalar : AlgebraicComplex)
  edge_ne_zero := one_ne_zero
  vertex_ne_zero := by
    intro zero
    apply D.nonzero
    exact Subtype.ext zero
  actual := nativeGraph_actual G D
  edge_exact := by simpa only [one_mul] using inverse_edge
  anchor_exact := by rw [nativeGraph_denote,InvertibleKernel.action_symm_action]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOrdinaryAnchorInput
end
