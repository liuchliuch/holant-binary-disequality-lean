import Holant.Proofs.Closure.Frontier

/-! Relative saved-forest closure, conditional on explicitly local leaves.
This module provides no unconditional complexity result, no classifier, and no
formal identification of its conclusion with the manuscript's global Close.
A consumer must supply one common target predicate, its proper-split closure,
and the listed local theorem at each exact current source-bound leaf domain. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierClosure
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Occurrences Frontier

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- These four local consumer hypotheses are intentionally still unproved.
The even domain includes every higher-arity prime, without a minimum-core
assumption. Binary safety and unary/odd complexity dispatch are not inferred
from the arity labels. Every domain identifies CURRENT P and its machines. -/
structure LocalLeafTheorems (P : Palette G) (C : AnySignature (OI.K G) → Prop) : Prop where
  unary : ∀ (o : Id G), CurrentDomain G P o →
    (originalLeaf G o).1.1 = 1 → C (originalLeaf G o).1
  binary : ∀ (o : Id G), CurrentDomain G P o →
    (originalLeaf G o).1.1 = 2 → C (originalLeaf G o).1
  oddNonbinary : ∀ (o : Id G), CurrentDomain G P o →
    3 ≤ (originalLeaf G o).1.1 → Odd (originalLeaf G o).1.1 → C (originalLeaf G o).1
  evenNonbinary : ∀ (o : Id G), CurrentDomain G P o →
    4 ≤ (originalLeaf G o).1.1 → Even (originalLeaf G o).1.1 → C (originalLeaf G o).1

/-- A genuinely local reconstruction rule for the same common predicate C.
It is not a caller-supplied certificate about the complete family. -/
def SplitClosed (C : AnySignature (OI.K G) → Prop) : Prop :=
  ∀ {f left right : AnySignature (OI.K G)}, ProperSplit f left right →
    C left → C right → C f

theorem leaf_conclusion (P : Palette G) (C : AnySignature (OI.K G) → Prop)
    (leaves : LocalLeafTheorems G P C) (o : Id G) : C (originalLeaf G o).1 := by
  let d := currentDomain G P o
  cases d.kind with
  | unary h => exact leaves.unary o d h
  | binary h => exact leaves.binary o d h
  | oddNonbinary hn ho => exact leaves.oddNonbinary o d hn ho
  | evenNonbinary hn he => exact leaves.evenNonbinary o d hn he

theorem current_leaf_conclusion (P : Palette G) (C : AnySignature (OI.K G) → Prop)
    (leaves : LocalLeafTheorems G P C) (o : Id G) :
    C (⟨P.arity (currentDomain G P o).currentLeafLabel.val,
      P.table (currentDomain G P o).currentLeafLabel⟩ : AnySignature (OI.K G)) := by
  rw [(currentDomain G P o).currentLeafExact]
  exact leaf_conclusion G P C leaves o

theorem factorTree_closed (C : AnySignature (OI.K G) → Prop) (splits : SplitClosed G C)
    {f : AnySignature (OI.K G)} (t : FactorTree f)
    (hleaf : ∀ p : Address t, C (leaf t p).1) : C f := by
  revert hleaf
  induction t with
  | leaf f hp =>
      intro hleaf
      exact hleaf ()
  | split data left right ihl ihr =>
      intro hleaf
      exact splits data (ihl (fun p => hleaf (.inl p))) (ihr (fun p => hleaf (.inr p)))

/-- The precise relative saved-family conclusion. All local leaf proofs are
explicit parameters; no unresolved domain is labelled as a resolved result. -/
theorem relative_saved_closure (P : Palette G) (C : AnySignature (OI.K G) → Prop)
    (splits : SplitClosed G C) (leaves : LocalLeafTheorems G P C) :
    ∀ f ∈ OI.family G, C f := by
  intro f hf
  rw [← Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.family_exact G] at hf
  obtain ⟨i, rfl⟩ := hf
  apply factorTree_closed G C splits (OI.storedTrees G i)
  intro p
  exact leaf_conclusion G P C leaves ⟨i, p⟩

/-- A concrete source consumer: if the separately checked local leaves are
all binary, the entire original saved family has actual CURRENT-P matching
presentations. This is not a complexity, common-basis, or global-Close claim. -/
theorem relative_original_matching (P : Palette G)
    (binaryLeaves : ∀ o : Id G, (originalLeaf G o).1.1 = 2) :
    ∀ f ∈ OI.family G,
      Holant.Certificates.MatchingContractionClosure.MatchingOrZero
        (Holant.Projective.BoundedTorsion.actualTransfers P.family) f.2 := by
  intro f hf
  rw [← Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.family_exact G] at hf
  obtain ⟨i, rfl⟩ := hf
  apply (OI.storedTrees G i).matchingOrZero P.family
  · intro leaf hleaf
    obtain ⟨p, hp⟩ := leaf_address_complete (OI.storedTrees G i) leaf hleaf
    let o : Id G := ⟨i, p⟩
    have he : (originalLeaf G o).1 = leaf := hp
    rw [← he]
    rw [← (currentDomain G P o).currentLeafExact]
    exact ⟨(currentDomain G P o).currentLeafLabel, rfl⟩
  · intro leaf hleaf
    obtain ⟨p, hp⟩ := leaf_address_complete (OI.storedTrees G i) leaf hleaf
    simpa only [originalLeaf, hp] using binaryLeaves ⟨i, p⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierClosure
end
