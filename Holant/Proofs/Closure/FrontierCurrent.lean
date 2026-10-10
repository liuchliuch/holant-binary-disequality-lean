import Holant.Proofs.Closure.OccurrenceCurrent

/-! Complete CURRENT-family pending frontier. Newly retained source primes are
included without changing or replacing the original saved-occurrence ledger. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.CurrentFrontier
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open CurrentOccurrences
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

def records (P : Palette G) : List ((o : Id G P) × Domain G P o) :=
  (enumeration G P).map (fun o => ⟨o, domain G P o⟩)

theorem records_complete (P : Palette G) (o : Id G P) :
    (⟨o, domain G P o⟩ : (o : Id G P) × Domain G P o) ∈ records G P :=
  List.mem_map.mpr ⟨o, enumeration_complete G P o, rfl⟩

theorem records_ids (P : Palette G) :
    (records G P).map Sigma.fst = enumeration G P := by
  simp [records, List.map_map, Function.comp_def]

theorem records_length (P : Palette G) :
    (records G P).length = Fintype.card (Id G P) := by
  simp [records, enumeration]

inductive Visit (P : Palette G) : Finset (Id G P) → Finset (Id G P) → Prop
  | erase (before : Finset (Id G P)) (o : Id G P) (pending : o ∈ before) :
      Visit P before (before.erase o)

theorem visit_decreases {P : Palette G} {before after : Finset (Id G P)}
    (h : Visit G P before after) : after.card < before.card := by
  cases h with | erase o ho => exact Finset.card_erase_lt_of_mem ho

theorem visit_wellFounded (P : Palette G) :
    WellFounded (fun after before => Visit G P before after) :=
  Subrelation.wf (fun h => visit_decreases G h) (measure Finset.card).wf

abbrev Runs (P : Palette G) := Relation.ReflTransGen (Visit G P)

theorem exhausts (P : Palette G) (before : Finset (Id G P)) : Runs G P before ∅ := by
  induction before using Finset.induction_on with
  | empty => exact .refl
  | @insert o todo ho ih =>
      have step : Visit G P (insert o todo) todo := by
        simpa [ho] using Visit.erase (P := P) (insert o todo) o (Finset.mem_insert_self o todo)
      exact (Relation.ReflTransGen.single step).trans ih

theorem visit_no_reopen {P : Palette G} {before after : Finset (Id G P)}
    (h : Visit G P before after) : after ⊆ before := by
  cases h with | erase o ho => exact Finset.erase_subset o before

theorem runs_no_reopen {P : Palette G} {before after : Finset (Id G P)}
    (h : Runs G P before after) : after ⊆ before := by
  induction h with
  | refl => exact fun _ h => h
  | tail h step ih => exact (visit_no_reopen G step).trans ih

structure Result (P : Palette G) where
  pending : List ((o : Id G P) × Domain G P o)
  pendingExact : pending = records G P
  original : Frontier.Result G P
  originalBindings : ∀ o : Occurrences.Id G, OriginalBinding G P o
  visitRun : Runs G P Finset.univ ∅

/-- Internal finite visit producer for all CURRENT saved prime occurrences,
plus the independently retained original occurrence ledger and bindings. -/
def build (P : Palette G) : Result G P :=
  ⟨records G P, rfl, Frontier.build G P, originalBinding G P, exhausts G P Finset.univ⟩

/-- Actual-history specialization replaces the weaker existential root
binding by the explicitly copied old-label receipt. The source producer owns
these labels and receipts; no closure or worklist policy is supplied here. -/
def buildAtRootLabels (P : Palette G) (labels : Fin (OI.count G) → Fin P.count)
    (saved : ∀ i : Fin (OI.count G), Frontier.paletteRoot G P (labels i) =
      (⟨⟨OI.arity G i.val, OI.publicTable G i⟩, OI.storedTrees G i⟩ : TreeOccurrence (OI.K G))) :
    Result G P := { build G P with originalBindings := bindingAt G P labels saved }

theorem buildAtRootLabels_original_injective (P : Palette G)
    (labels : Fin (OI.count G) → Fin P.count) (injective : Function.Injective labels)
    (saved : ∀ i : Fin (OI.count G), Frontier.paletteRoot G P (labels i) =
      (⟨⟨OI.arity G i.val, OI.publicTable G i⟩, OI.storedTrees G i⟩ : TreeOccurrence (OI.K G))) :
    Function.Injective (fun o : Occurrences.Id G =>
      ((buildAtRootLabels G P labels saved).originalBindings o).current) :=
  bindingAt_injective G P labels injective saved

theorem build_current_coverage (P : Palette G) (o : Id G P) :
    (⟨o, domain G P o⟩ : (o : Id G P) × Domain G P o) ∈ (build G P).pending :=
  records_complete G P o

theorem build_original_coverage (P : Palette G) (o : Occurrences.Id G) :
    (⟨o, Frontier.currentDomain G P o⟩ :
      (o : Occurrences.Id G) × Frontier.CurrentDomain G P o) ∈ (build G P).original.pending :=
  Frontier.build_coverage G P o

end Holant.LocalDrafts.RemoteWork.StableClosureV2.CurrentFrontier
end
