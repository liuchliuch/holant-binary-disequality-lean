import Holant.Proofs.Closure.ClosureFactorTreeFieldMap
import Holant.Proofs.Closure.HistoryPalette

/-! NEW POST-RECOVERY SOURCE; fresh strict verification is required.
Thin specialization of the lead's generic structural transport to ACTUAL
current palette roots and the exact returned original-label history embedding.
No new factorization is chosen and no marked coordinate table becomes an oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.HistoryMappedTrees
open Holant Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

def saved (P : Palette G) (i : Fin P.count) : TreeOccurrence (OI.K G) :=
  ⟨⟨P.arity i.val,P.table i⟩,P.trees i⟩

def markedSaved (P : Palette G) (phi : OI.K G →+* AlgebraicComplex)
    (B : InvertibleKernel) (i : Fin P.count) : TreeOccurrence AlgebraicComplex :=
  ClosureFactorTreeAction.occurrence B (ClosureFactorTreeFieldMap.occurrence phi (saved G P i))

def markedSlots (P : Palette G) (phi : OI.K G →+* AlgebraicComplex)
    (B : InvertibleKernel) (i : Fin P.count) :
    FactorSaturation.Slots (P.trees i) ≃ FactorSaturation.Slots (markedSaved G P phi B i).2 :=
  ClosureFactorTreeFieldMap.markedSlots phi B (P.trees i)

def markedLeaves (P : Palette G) (phi : OI.K G →+* AlgebraicComplex)
    (B : InvertibleKernel) (i : Fin P.count) :
    FactorSaturation.Leaves (P.trees i) ≃ FactorSaturation.Leaves (markedSaved G P phi B i).2 :=
  ClosureFactorTreeFieldMap.markedLeaves phi B (P.trees i)

theorem leaf_exact (P : Palette G) (phi : OI.K G →+* AlgebraicComplex)
    (B : InvertibleKernel) (i : Fin P.count) (u : FactorSaturation.Leaves (P.trees i)) :
    FactorSaturation.leaf (markedSaved G P phi B i).2 (markedLeaves G P phi B i u) =
      ClosureFactorTreeAction.signature B (mapSignature phi (FactorSaturation.leaf (P.trees i) u)) :=
  ClosureFactorTreeFieldMap.marked_leaf_exact phi B (P.trees i) u

theorem leaf_card (P : Palette G) (phi : OI.K G →+* AlgebraicComplex)
    (B : InvertibleKernel) (i : Fin P.count) :
    Fintype.card (FactorSaturation.Leaves (markedSaved G P phi B i).2) =
      Fintype.card (FactorSaturation.Leaves (P.trees i)) :=
  ClosureFactorTreeFieldMap.marked_leaf_card phi B (P.trees i)

theorem path_exact (P : Palette G) (phi : OI.K G →+* AlgebraicComplex)
    (B : InvertibleKernel) (i : Fin P.count) (u : FactorSaturation.Slots (P.trees i)) :
    FactorSaturation.path (markedSaved G P phi B i).2 (markedSlots G P phi B i u) =
      FactorSaturation.path (P.trees i) u :=
  ClosureFactorTreeFieldMap.marked_path_exact phi B (P.trees i) u

theorem slot_exact (P : Palette G) (phi : OI.K G →+* AlgebraicComplex)
    (B : InvertibleKernel) (i : Fin P.count) (u : FactorSaturation.Slots (P.trees i)) :
    FactorSaturation.slot (markedSaved G P phi B i).2 (markedSlots G P phi B i u) =
      ClosureFactorTreeAction.occurrence B
        (ClosureFactorTreeFieldMap.occurrence phi (FactorSaturation.slot (P.trees i) u)) :=
  ClosureFactorTreeFieldMap.marked_slot_exact phi B (P.trees i) u

/-- The exact original tree, including duplicate root IDs, is transported at
its ACTUAL returned final label. No generic originalSaved choice substitutes it. -/
theorem original_exact (torsion : ResidualTorsion (OI.family G)) (core : MinimumCore (OI.family G))
    (proper : 4 ≤ core.signature.1) (even : Even core.signature.1)
    (phi : OI.K G →+* AlgebraicComplex) (B : InvertibleKernel) (i : Fin (OI.count G)) :
    markedSaved G (HistoryPalette.original G torsion core proper even).palette phi B
      (HistoryPalette.originalLabel G torsion core proper even i) =
        ClosureFactorTreeAction.occurrence B (ClosureFactorTreeFieldMap.occurrence phi
          ⟨⟨OI.arity G i.val,OI.publicTable G i⟩,OI.storedTrees G i⟩) := by
  exact congrArg (fun o => ClosureFactorTreeAction.occurrence B
    (ClosureFactorTreeFieldMap.occurrence phi o))
      (HistoryPalette.originalSavedAt G torsion core proper even i)

/-- The actual original coefficient embedding, at the exact saved original
label in the returned physical history. No alternative field is selected. -/
theorem original_embedding_exact (torsion : ResidualTorsion (OI.family G))
    (core : MinimumCore (OI.family G)) (proper : 4 ≤ core.signature.1)
    (even : Even core.signature.1) (B : InvertibleKernel) (i : Fin (OI.count G)) :
    markedSaved G (HistoryPalette.original G torsion core proper even).palette
      (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom B (HistoryPalette.originalLabel G torsion core proper even i) =
        ClosureFactorTreeAction.occurrence B (ClosureFactorTreeFieldMap.occurrence
          (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom ⟨⟨OI.arity G i.val,OI.publicTable G i⟩,OI.storedTrees G i⟩) :=
  original_exact G torsion core proper even (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G).toRingHom B i

theorem original_labels_injective (torsion : ResidualTorsion (OI.family G))
    (core : MinimumCore (OI.family G)) (proper : 4 ≤ core.signature.1) (even : Even core.signature.1) :
    Function.Injective (HistoryPalette.originalLabel G torsion core proper even) :=
  HistoryPalette.originalLabel_injective G torsion core proper even

end Holant.LocalDrafts.RemoteWork.StableClosureV2.HistoryMappedTrees
end
