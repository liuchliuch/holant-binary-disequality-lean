import Holant.Proofs.Closure.HistoryMappedTrees
import Holant.Marked.Fusion

/-! NEW_POST_RECOVERY; pending fresh strict check. Actual sector convention
for the returned saved history: marked transport U uses U.symm.action and
sectorEdge U, exactly the inverse-basis argument of physical holographic
return. The generic supplied-tree transport is reused unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorTrees
open Holant Holant.Tractable Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness
namespace RH
export Holant.LocalDrafts.MainChain.RingHomRealization (mapAny mapFamily)
end RH
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

def saved (P : Palette G) (phi : OI.K G →+* AlgebraicComplex) (U : InvertibleKernel)
    (i : Fin P.count) : TreeOccurrence AlgebraicComplex :=
  HistoryMappedTrees.markedSaved G P phi U.symm i

def slots (P : Palette G) (phi : OI.K G →+* AlgebraicComplex) (U : InvertibleKernel)
    (i : Fin P.count) : FactorSaturation.Slots (P.trees i) ≃ FactorSaturation.Slots (saved G P phi U i).2 :=
  HistoryMappedTrees.markedSlots G P phi U.symm i

def leaves (P : Palette G) (phi : OI.K G →+* AlgebraicComplex) (U : InvertibleKernel)
    (i : Fin P.count) : FactorSaturation.Leaves (P.trees i) ≃ FactorSaturation.Leaves (saved G P phi U i).2 :=
  HistoryMappedTrees.markedLeaves G P phi U.symm i

theorem path_exact (P : Palette G) (phi : OI.K G →+* AlgebraicComplex) (U : InvertibleKernel)
    (i : Fin P.count) (j : FactorSaturation.Slots (P.trees i)) :
    FactorSaturation.path (saved G P phi U i).2 (slots G P phi U i j) =
      FactorSaturation.path (P.trees i) j :=
  HistoryMappedTrees.path_exact G P phi U.symm i j

theorem leaf_exact (P : Palette G) (phi : OI.K G →+* AlgebraicComplex) (U : InvertibleKernel)
    (i : Fin P.count) (j : FactorSaturation.Leaves (P.trees i)) :
    FactorSaturation.leaf (saved G P phi U i).2 (leaves G P phi U i j) =
      ClosureFactorTreeAction.signature U.symm (mapSignature phi (FactorSaturation.leaf (P.trees i) j)) :=
  HistoryMappedTrees.leaf_exact G P phi U.symm i j

/-- Only roots and actual retained prime leaves are claimed family labels;
composite interior nodes retain their separate charged access boundary. -/
theorem root_member (P : Palette G) (phi : OI.K G →+* AlgebraicComplex) (U : InvertibleKernel)
    (i : Fin P.count) : (saved G P phi U i).1 ∈ familyAction U.symm (RH.mapFamily phi P.family) := by
  refine ⟨RH.mapAny phi ⟨P.arity i.val,P.table i⟩,?_,rfl⟩
  exact ⟨⟨P.arity i.val,P.table i⟩,⟨i,rfl⟩,rfl⟩

theorem leaf_member (P : Palette G) (phi : OI.K G →+* AlgebraicComplex) (U : InvertibleKernel)
    (i : Fin P.count) (j : FactorSaturation.Leaves (P.trees i)) :
    FactorSaturation.leaf (saved G P phi U i).2 (leaves G P phi U i j) ∈
      familyAction U.symm (RH.mapFamily phi P.family) := by
  rw [leaf_exact]
  refine ⟨RH.mapAny phi (FactorSaturation.leaf (P.trees i) j),?_,rfl⟩
  exact ⟨FactorSaturation.leaf (P.trees i) j,
    P.leavesRetained i _ (FactorSaturation.leaf_mem (P.trees i) j),rfl⟩

/-- This is exactly the physical inverse-holographic edge hypothesis when
its basis argument is U.symm. All scalars in sectorEdge U are retained. -/
theorem same_edge (U : InvertibleKernel) :
    Kernel.pullback Signature.disequality U.symm.inverse = sectorEdge U := rfl

theorem binary_transport (U : InvertibleKernel) (B : Mat) :
    U.symm.action (kernelSignature B) = kernelSignature (transport U B) :=
  transport_signature U B

theorem original_exact (torsion : ResidualTorsion (OI.family G))
    (core : MinimumCore (OI.family G)) (proper : 4 ≤ core.signature.1)
    (even : Even core.signature.1) (U : InvertibleKernel) (i : Fin (OI.count G)) :
    saved G (HistoryPalette.original G torsion core proper even).palette
      (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom U
      (HistoryPalette.originalLabel G torsion core proper even i) =
        ClosureFactorTreeAction.occurrence U.symm (ClosureFactorTreeFieldMap.occurrence
          (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom
          ⟨⟨OI.arity G i.val,OI.publicTable G i⟩,OI.storedTrees G i⟩) :=
  HistoryMappedTrees.original_embedding_exact G torsion core proper even U.symm i

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistorySectorTrees
end
