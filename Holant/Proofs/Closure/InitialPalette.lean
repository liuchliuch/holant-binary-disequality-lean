import Holant.Proofs.Closure.InitialProgrammes
import Holant.Proofs.Closure.PhysicalCosts

/-! The actual initial palette retains every exact original saved factor tree.
No replacement factorization, source field, or externally supplied compiler is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.Initial
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
attribute [local irreducible] InitialProgrammes.toOriginal InitialProgrammes.fromOriginal

/-- Closed initial physical palette factory for the original fixed family. -/
def palette : Palette G where
  count := OI.count G
  arity := OI.arity G
  table := OI.publicTable G
  positive := OriginalFrozenForest.OriginalInput.positive G
  nonzero := OriginalFrozenForest.OriginalInput.nonzero G
  trees := OI.storedTrees G
  leavesRetained i f hf := by
    rw [OriginalFrozenForest.OriginalInput.family_exact]
    exact OriginalFrozenForest.OriginalInput.storedTrees_leaves G i f hf
  originalSaved i := ⟨i,rfl⟩
  equality := by
    rw [OriginalFrozenForest.OriginalInput.family_exact]
    exact OriginalFrozenForest.OriginalInput.retains_identity G
  toOriginal := PhysicalProgramme.ofControlled (InitialProgrammes.toOriginal G)
  fromOriginal := PhysicalProgramme.ofControlled (InitialProgrammes.fromOriginal G)

@[simp] theorem family_exact : (palette G).family = OI.family G :=
  OriginalFrozenForest.OriginalInput.family_exact G
@[simp] theorem count_exact : (palette G).count = OI.count G := rfl
@[simp] theorem table_exact : (palette G).table = OI.publicTable G := rfl
@[simp] theorem trees_exact (i : Fin (OI.count G)) :
    HEq ((palette G).trees i) (OI.storedTrees G i) := HEq.rfl

theorem saturated : FactorSaturated (palette G).family := by
  rw [family_exact]
  exact OriginalFrozenForest.OriginalInput.saturated G

/-- Exact full occurrence equality, stronger than equality of root tables. -/
theorem saved_occurrence (i : Fin (OI.count G)) :
    (⟨⟨(palette G).arity i.val,(palette G).table i⟩,(palette G).trees i⟩ :
      TreeOccurrence (OI.K G)) =
      ⟨⟨OI.arity G i.val,OI.publicTable G i⟩,OI.storedTrees G i⟩ := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.Initial
