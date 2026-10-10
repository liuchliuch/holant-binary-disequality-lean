import Holant.Proofs.Closure.ClosureMarkedSourceRouting
import Holant.Proofs.Closure.HistorySectorTrees
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpen

/-! NEW_POST_RECOVERY; pending fresh strict verification. The closed actual
source marking is paired with its SAME U.symm saved trees, actual sector edge
and separately charged original-G open-return factory. This neither identifies
an X-native regenerated deck with the marked deck nor makes U a gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedHistoryReceipts
open Holant Holant.Tractable Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness
open ClosurePhysicalBridge
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapFamily)
end RH
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- All payloads use the actual source palette and the SAME sector basis.
Open return consumes a genuine graph with literal changed source labels and
that exact edge, and returns the already proved original-G physical access. -/
structure SectorReceipt (P : Palette G) (U : InvertibleKernel) : Type 1 where
  saved : Fin P.count → TreeOccurrence AlgebraicComplex
  savedIdentity : ∀ i, saved i = HistorySectorTrees.saved G P (algebraicEmbedding G) U i
  slots : ∀ i, FactorSaturation.Slots (P.trees i) ≃ FactorSaturation.Slots (saved i).2
  path : ∀ i j, FactorSaturation.path (saved i).2 (slots i j) = FactorSaturation.path (P.trees i) j
  leaves : ∀ i, FactorSaturation.Leaves (P.trees i) ≃ FactorSaturation.Leaves (saved i).2
  rootLabels : ∀ i, (saved i).1 ∈ familyAction U.symm (RH.mapFamily (algebraicEmbedding G) P.family)
  leafLabels : ∀ i j, FactorSaturation.leaf (saved i).2 (leaves i j) ∈
    familyAction U.symm (RH.mapFamily (algebraicEmbedding G) P.family)
  edge : Mat
  edgeIdentity : edge = sectorEdge U
  openReturn : ∀ {n : ℕ} (N : Network AlgebraicComplex n)
    (labels : ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex) ∈
      familyAction U.symm (RH.mapFamily (algebraicEmbedding G) P.family))
    (edges : ∀ e, N.edge e = edge), HolographicOpenAccess G P U.symm N

/-- The source trees, edge and full physical-return function are constructed;
no replacement factorization, basis resource or compiler is caller input. -/
def sectorReceipt (P : Palette G) (U : InvertibleKernel) : SectorReceipt G P U where
  saved := HistorySectorTrees.saved G P (algebraicEmbedding G) U
  savedIdentity _ := rfl
  slots := HistorySectorTrees.slots G P (algebraicEmbedding G) U
  path := HistorySectorTrees.path_exact G P (algebraicEmbedding G) U
  leaves := HistorySectorTrees.leaves G P (algebraicEmbedding G) U
  rootLabels := HistorySectorTrees.root_member G P (algebraicEmbedding G) U
  leafLabels := HistorySectorTrees.leaf_member G P (algebraicEmbedding G) U
  edge := sectorEdge U
  edgeIdentity := rfl
  openReturn N labels edges := fromHolographicOpen G P U.symm N labels
    (fun e => (edges e).trans (HistorySectorTrees.same_edge U).symm)

def ReceiptFor (P : Palette G) (torsion : ResidualTorsion P.family)
    (M : ClosureMarkedSourceRouting.Marking (algebraicEmbedding G) P.family torsion) : Type 1 :=
  match M.basis with
  | none => PUnit.{2}
  | some U => SectorReceipt G P U

structure Result (P : Palette G) (torsion : ResidualTorsion P.family) : Type 1 where
  marking : ClosureMarkedSourceRouting.Marking (algebraicEmbedding G) P.family torsion
  markingIdentity : marking = ClosureMarkedSourceRouting.produce (algebraicEmbedding G) P.family torsion P.equality
  receipts : ReceiptFor G P torsion marking

/-- Closed on the already established actual source palette. The basis,
phase/model selection and every applicable receipt are constructed internally.
Genuine small-group and semantic Platonic alternatives keep their own payload. -/
def produce (P : Palette G) (torsion : ResidualTorsion P.family) : Result G P torsion := by
  let M := ClosureMarkedSourceRouting.produce (algebraicEmbedding G) P.family torsion P.equality
  refine ⟨M,rfl,?_⟩
  unfold ReceiptFor
  cases hb : M.basis with
  | none => exact PUnit.unit
  | some U => exact sectorReceipt G P U

/-- The actual edge and inverse-basis convention of the stored return factory. -/
theorem same_physical_edge (P : Palette G) (U : InvertibleKernel) :
    (sectorReceipt G P U).edge = Kernel.pullback Signature.disequality U.symm.inverse := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureMarkedHistoryReceipts
end
