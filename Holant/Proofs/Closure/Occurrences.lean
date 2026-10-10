import Holant.Proofs.Closure.Interface
import Holant.Proofs.Closure.OccurrenceAddresses
import Mathlib.Data.Fintype.BigOperators

/-! RECONSTRUCTED after executor loss; recheck required. Exact original saved
root indices plus branch addresses retain every prime occurrence and duplicate. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.Occurrences
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

abbrev Id := (i : Fin (OI.count G)) × Address (OI.storedTrees G i)
instance idDecidableEq : DecidableEq (Id G) := Classical.decEq _

def originalRoot (o : Id G) : TreeOccurrence (OI.K G) :=
  ⟨⟨OI.arity G o.1.val, OI.publicTable G o.1⟩, OI.storedTrees G o.1⟩
def originalLeaf (o : Id G) : TreeOccurrence (OI.K G) := leaf (OI.storedTrees G o.1) o.2

theorem originalLeaf_stored (o : Id G) : StoredSubtree (originalLeaf G o) (originalRoot G o) :=
  leaf_stored (OI.storedTrees G o.1) o.2
theorem originalLeaf_prime (o : Id G) : Prime (originalLeaf G o).1 :=
  leaf_prime (OI.storedTrees G o.1) o.2
theorem originalLeaf_positive (o : Id G) : 0 < (originalLeaf G o).1.1 :=
  leaf_positive (OI.storedTrees G o.1)
    (Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.positive G o.1) o.2
theorem originalLeaf_retained (o : Id G) : (originalLeaf G o).1 ∈ OI.family G :=
  Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.storedTrees_leaves G o.1 _
    (leaf_mem (OI.storedTrees G o.1) o.2)

theorem different_roots_distinguish (i j : Fin (OI.count G))
    (p : Address (OI.storedTrees G i)) (q : Address (OI.storedTrees G j)) (hne : i ≠ j) :
    (⟨i,p⟩ : Id G) ≠ ⟨j,q⟩ := fun he => hne (congrArg Sigma.fst he)
theorem different_addresses_distinguish (i : Fin (OI.count G))
    (p q : Address (OI.storedTrees G i)) (hne : p ≠ q) : (⟨i,p⟩ : Id G) ≠ ⟨i,q⟩ := by
  intro he
  exact hne (@sigma_mk_injective (Fin (OI.count G)) (fun j => Address (OI.storedTrees G j)) i p q he)

theorem id_card : Fintype.card (Id G) = ∑ i : Fin (OI.count G), (OI.storedTrees G i).leaves.card := by
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun i _ => address_card (OI.storedTrees G i))
def enumeration : List (Id G) :=
  List.ofFn (fun i : Fin (Fintype.card (Id G)) => (Fintype.equivFin (Id G)).symm i)
theorem enumeration_complete (o : Id G) : o ∈ enumeration G := by
  simp only [enumeration, List.mem_ofFn]
  exact ⟨(Fintype.equivFin (Id G)) o, Equiv.symm_apply_apply _ _⟩
theorem enumeration_nodup : (enumeration G).Nodup := List.nodup_ofFn.mpr (Equiv.injective _)
theorem enumeration_length : (enumeration G).length = Fintype.card (Id G) := by simp [enumeration]
theorem higher_arity_not_discarded (o : Id G) (_higher : 4 ≤ (originalLeaf G o).1.1) :
    o ∈ enumeration G := enumeration_complete G o

end Holant.LocalDrafts.RemoteWork.StableClosureV2.Occurrences
end
