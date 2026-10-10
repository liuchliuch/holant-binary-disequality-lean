import Holant.Proofs.Closure.Frontier
import Mathlib.Data.Fintype.BigOperators

/-! Saved prime occurrences in the entire CURRENT physical palette, including
newly retained primes. This is additional to the original-ID ledger; none of
its local domains is treated as already classified. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.CurrentOccurrences
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

abbrev Id (P : Palette G) := (i : Fin P.count) × Occurrences.Address (P.trees i)
instance idDecidableEq (P : Palette G) : DecidableEq (Id G P) := Classical.decEq _

def savedRoot (P : Palette G) (o : Id G P) : TreeOccurrence (OI.K G) :=
  Frontier.paletteRoot G P o.1

def savedLeaf (P : Palette G) (o : Id G P) : TreeOccurrence (OI.K G) :=
  Occurrences.leaf (P.trees o.1) o.2

theorem savedLeaf_stored (P : Palette G) (o : Id G P) :
    StoredSubtree (savedLeaf G P o) (savedRoot G P o) :=
  Occurrences.leaf_stored (P.trees o.1) o.2

theorem savedLeaf_prime (P : Palette G) (o : Id G P) : Prime (savedLeaf G P o).1 :=
  Occurrences.leaf_prime (P.trees o.1) o.2

theorem savedLeaf_positive (P : Palette G) (o : Id G P) : 0 < (savedLeaf G P o).1.1 :=
  Occurrences.leaf_positive (P.trees o.1) (P.positive o.1) o.2

theorem savedLeaf_retained (P : Palette G) (o : Id G P) :
    (savedLeaf G P o).1 ∈ P.family :=
  P.leavesRetained o.1 _ (Occurrences.leaf_mem (P.trees o.1) o.2)

def enumeration (P : Palette G) : List (Id G P) :=
  List.ofFn (fun i : Fin (Fintype.card (Id G P)) => (Fintype.equivFin (Id G P)).symm i)

theorem enumeration_complete (P : Palette G) (o : Id G P) : o ∈ enumeration G P := by
  simp only [enumeration, List.mem_ofFn]
  exact ⟨(Fintype.equivFin (Id G P)) o, Equiv.symm_apply_apply _ _⟩

theorem enumeration_nodup (P : Palette G) : (enumeration G P).Nodup :=
  List.nodup_ofFn.mpr (Equiv.injective _)

theorem id_card (P : Palette G) : Fintype.card (Id G P) =
    ∑ i : Fin P.count, (P.trees i).leaves.card := by
  rw [Fintype.card_sigma]
  exact Finset.sum_congr rfl (fun i _ => Occurrences.address_card (P.trees i))

/-- All current leaves are pending at their exact P source boundary. -/
structure Domain (P : Palette G) (o : Id G P) where
  label : Fin P.count
  literal : (⟨P.arity label.val, P.table label⟩ : AnySignature (OI.K G)) = (savedLeaf G P o).1
  kind : Frontier.LocalKind G (savedLeaf G P o).1
  preparation : Frontier.Preparation G P (savedLeaf G P o).1

abbrev Domain.toOriginal {P : Palette G} {o : Id G P} (_domain : Domain G P o) := P.toOriginal
abbrev Domain.fromOriginal {P : Palette G} {o : Id G P} (_domain : Domain G P o) := P.fromOriginal

theorem Domain.toOriginal_same_machine {P : Palette G} {o : Id G P} (d : Domain G P o) :
    (Domain.toOriginal G d).controlled.reduction.machine = P.toOriginal.controlled.reduction.machine := rfl

theorem Domain.fromOriginal_same_machine {P : Palette G} {o : Id G P} (d : Domain G P o) :
    (Domain.fromOriginal G d).controlled.reduction.machine = P.fromOriginal.controlled.reduction.machine := rfl

def domain (P : Palette G) (o : Id G P) : Domain G P o := by
  have hlabels : ∃ j : Fin P.count,
      (⟨P.arity j.val, P.table j⟩ : AnySignature (OI.K G)) = (savedLeaf G P o).1 :=
    savedLeaf_retained G P o
  let j := Classical.choose hlabels
  exact ⟨j, Classical.choose_spec hlabels,
    Frontier.classify G (savedLeaf G P o).1 (savedLeaf_positive G P o), .pending⟩

def Domain.withMinimum {P : Palette G} {o : Id G P} (d : Domain G P o)
    (minimum : MinimumCore P.family) (literal : minimum.signature = (savedLeaf G P o).1) :
    Domain G P o := { d with preparation := .actualMinimum minimum literal }

theorem domain_unprepared (P : Palette G) (o : Id G P) :
    (domain G P o).preparation = Frontier.Preparation.pending := rfl

/-- Original identities remain in their separate ledger. Their binding into
P is equality of the complete saved root and the exact transported leaf tree. -/
structure OriginalBinding (P : Palette G) (o : Occurrences.Id G) where
  rootLabel : Fin P.count
  rootExact : Frontier.paletteRoot G P rootLabel = Occurrences.originalRoot G o
  current : Id G P
  currentRoot : current.1 = rootLabel
  addressExact : HEq current.2 (Occurrences.transportAddress rootExact.symm o.2)
  leafExact : savedLeaf G P current = Occurrences.originalLeaf G o

def originalBinding (P : Palette G) (o : Occurrences.Id G) : OriginalBinding G P o := by
  let j := Classical.choose (P.originalSaved o.1)
  have rootExact : Frontier.paletteRoot G P j = Occurrences.originalRoot G o :=
    Classical.choose_spec (P.originalSaved o.1)
  let p := Occurrences.transportAddress rootExact.symm o.2
  exact ⟨j, rootExact, ⟨j, p⟩, rfl, HEq.rfl,
    Occurrences.transportAddress_leaf rootExact.symm o.2⟩

/-- Explicit actual-history root-label binding. The closed history supplies
these exact old-label receipts internally, rather than existentially choosing
another current label with an equal root/tree. -/
def bindingAt (P : Palette G) (labels : Fin (OI.count G) → Fin P.count)
    (saved : ∀ i : Fin (OI.count G), Frontier.paletteRoot G P (labels i) =
      (⟨⟨OI.arity G i.val, OI.publicTable G i⟩, OI.storedTrees G i⟩ : TreeOccurrence (OI.K G)))
    (o : Occurrences.Id G) : OriginalBinding G P o :=
  let p := Occurrences.transportAddress (saved o.1).symm o.2
  ⟨labels o.1, saved o.1, ⟨labels o.1, p⟩, rfl, HEq.rfl,
    Occurrences.transportAddress_leaf (saved o.1).symm o.2⟩

theorem bindingAt_injective (P : Palette G) (labels : Fin (OI.count G) → Fin P.count)
    (injective : Function.Injective labels)
    (saved : ∀ i : Fin (OI.count G), Frontier.paletteRoot G P (labels i) =
      (⟨⟨OI.arity G i.val, OI.publicTable G i⟩, OI.storedTrees G i⟩ : TreeOccurrence (OI.K G))) :
    Function.Injective (fun o : Occurrences.Id G => (bindingAt G P labels saved o).current) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ he
  have hi : labels i = labels j := congrArg Sigma.fst he
  have hij := injective hi
  subst j
  have ha : Occurrences.transportAddress (saved i).symm p =
      Occurrences.transportAddress (saved i).symm q :=
    @sigma_mk_injective (Fin P.count) (fun k => Occurrences.Address (P.trees k))
      (labels i) _ _ he
  have hpq := Occurrences.transportAddress_injective (saved i).symm ha
  exact Sigma.ext rfl (heq_of_eq hpq)

/-- Different saved root/tree choices cannot alias one current root label. -/
theorem distinct_original_trees_never_alias (P : Palette G) (o p : Occurrences.Id G)
    (hne : Occurrences.originalRoot G o ≠ Occurrences.originalRoot G p) :
    (originalBinding G P o).rootLabel ≠ (originalBinding G P p).rootLabel := by
  intro he
  have currentEq := congrArg (Frontier.paletteRoot G P) he
  exact hne ((originalBinding G P o).rootExact.symm.trans
    (currentEq.trans (originalBinding G P p).rootExact))

/-- Literal family retention follows from exact old-root/tree bindings. -/
theorem original_family_retained (P : Palette G) : OI.family G ⊆ P.family := by
  intro f hf
  rw [← Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.family_exact G] at hf
  obtain ⟨i, rfl⟩ := hf
  obtain ⟨j, hj⟩ := P.originalSaved i
  exact ⟨j, congrArg Sigma.fst hj⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.CurrentOccurrences
end
