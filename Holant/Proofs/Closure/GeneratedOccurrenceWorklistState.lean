import Holant.Proofs.Closure.GeneratedOccurrenceWorklistPartition
import Holant.Proofs.Closure.GeneratedOccurrenceWorklistBookkeeping
import Holant.Proofs.Closure.OccurrenceWorklistLedger

/-! Current addressed preparation ledger with recursive generation of strictly
lower-arity work. Complete old trees are copied injectively; old prepared IDs
never become fresh work. The actual returned batch's NEW addresses are scheduled
once, with multiplicity represented by physical root/address IDs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)

structure State : Type 1 where
  palette : Palette G
  rootLabel : Fin base.count → Fin palette.count
  rootInjective : Function.Injective rootLabel
  rootSaved : ∀ i, Frontier.paletteRoot G palette (rootLabel i) = Frontier.paletteRoot G base i
  todo : Finset (CurrentOccurrences.Id G palette)
  done : Finset (CurrentOccurrences.Id G palette)
  disjoint : Disjoint todo done
  partition : todo ∪ done = Finset.univ

def initial : State G base := ⟨base,id,Function.injective_id,fun _ => rfl,Finset.univ,∅,by simp,by simp⟩

def State.currentId (S : State G base) (o : CurrentOccurrences.Id G base) : CurrentOccurrences.Id G S.palette :=
  ⟨S.rootLabel o.1,Occurrences.transportAddress (S.rootSaved o.1).symm o.2⟩

theorem State.leafExact (S : State G base) (o : CurrentOccurrences.Id G base) :
    CurrentOccurrences.savedLeaf G S.palette (S.currentId G base o) = CurrentOccurrences.savedLeaf G base o :=
  Occurrences.transportAddress_leaf (S.rootSaved o.1).symm o.2

def weight (P : Palette G) (o : CurrentOccurrences.Id G P) : ℕ := (CurrentOccurrences.savedLeaf G P o).1.1

def State.rank (S : State G base) : Multiset ℕ := arityRank (weight G S.palette) S.todo

abbrev Input (P : Palette G) (o : CurrentOccurrences.Id G P) :=
  OccurrenceWorklist.BatchInput G P (OccurrenceWorklist.initial G P) o

abbrev Next (P : Palette G) (torsion : ResidualTorsion P.family) {m : ℕ}
    (f : Signature (OI.K G) (m+2)) (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family) (hm : 2 ≤ m) :=
  GeneratedOccurrenceWorklistPartition.palette G P torsion f retained hm

def copy (P : Palette G) (torsion : ResidualTorsion P.family) {m : ℕ}
    (f : Signature (OI.K G) (m+2)) (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family) (hm : 2 ≤ m) :
    CurrentOccurrences.Id G P ↪ CurrentOccurrences.Id G (Next G P torsion f retained hm) :=
  GeneratedOccurrenceWorklistPartition.copyEmbedding G P torsion f retained hm

theorem copy_disjoint_new (P : Palette G) (torsion : ResidualTorsion P.family) {m : ℕ}
    (f : Signature (OI.K G) (m+2)) (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family) (hm : 2 ≤ m) :
    Disjoint (Finset.univ.map (copy G P torsion f retained hm))
      (GeneratedOccurrenceWorklistPartition.newIds G P torsion f retained hm) := by
  exact GeneratedOccurrenceWorklistPartition.copy_disjoint_new G P torsion f retained hm

theorem copy_new_partition (P : Palette G) (torsion : ResidualTorsion P.family) {m : ℕ}
    (f : Signature (OI.K G) (m+2)) (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family) (hm : 2 ≤ m) :
    Finset.univ.map (copy G P torsion f retained hm) ∪
      GeneratedOccurrenceWorklistPartition.newIds G P torsion f retained hm = Finset.univ := by
  exact GeneratedOccurrenceWorklistPartition.copied_new_partition G P torsion f retained hm

def State.binary (S : State G base) (o : CurrentOccurrences.Id G S.palette) (pending : o ∈ S.todo) : State G base :=
  { S with
    todo := S.todo.erase o
    done := insert o S.done
    disjoint := erase_insert_disjoint S.todo S.done S.disjoint o
    partition := erase_insert_partition S.todo S.done S.partition o pending }

theorem State.higherDisjoint (S : State G base) (o : CurrentOccurrences.Id G S.palette)
    (b : Input G S.palette o) (torsion : ResidualTorsion S.palette.family) :
    Disjoint ((S.todo.erase o).map (copy G S.palette torsion b.signature b.retained b.proper))
      (GeneratedOccurrenceWorklistPartition.newIds G S.palette torsion b.signature b.retained b.proper) :=
  map_disjoint_fresh _ _ (copy_disjoint_new G S.palette torsion b.signature b.retained b.proper) _

def State.higher (S : State G base) (o : CurrentOccurrences.Id G S.palette) (pending : o ∈ S.todo)
    (b : Input G S.palette o) (torsion : ResidualTorsion S.palette.family) : State G base where
  palette := Next G S.palette torsion b.signature b.retained b.proper
  rootLabel i := RetainedCatalogue.oldLabel G S.palette torsion b.signature (S.rootLabel i)
  rootInjective := by
    intro i j h
    apply S.rootInjective
    apply Fin.ext
    exact congrArg (fun x : Fin (RetainedCatalogue.count G S.palette torsion b.signature) => x.val) h
  rootSaved i := (RetainedCatalogue.old_saved G S.palette torsion b.signature (S.rootLabel i)).trans (S.rootSaved i)
  todo := ((S.todo.erase o).map (copy G S.palette torsion b.signature b.retained b.proper)).disjUnion
    (GeneratedOccurrenceWorklistPartition.newIds G S.palette torsion b.signature b.retained b.proper)
    (S.higherDisjoint G base o b torsion)
  done := (insert o S.done).map (copy G S.palette torsion b.signature b.retained b.proper)
  disjoint := replacement_disjoint _ _ (copy_disjoint_new G S.palette torsion b.signature b.retained b.proper)
    S.todo S.done S.disjoint o (S.higherDisjoint G base o b torsion)
  partition := replacement_partition _ _ (copy_new_partition G S.palette torsion b.signature b.retained b.proper)
    S.todo S.done S.partition o pending (S.higherDisjoint G base o b torsion)

theorem State.binary_decreases (S : State G base) (o : CurrentOccurrences.Id G S.palette) (pending : o ∈ S.todo) :
    Multiset.IsDershowitzMannaLT ((S.binary G base o pending).rank G base) (S.rank G base) :=
  erasure_decreases (weight G S.palette) S.todo o pending

theorem State.higher_decreases (S : State G base) (o : CurrentOccurrences.Id G S.palette) (pending : o ∈ S.todo)
    (b : Input G S.palette o) (torsion : ResidualTorsion S.palette.family) :
    Multiset.IsDershowitzMannaLT ((S.higher G base o pending b torsion).rank G base) (S.rank G base) := by
  apply replacement_decreases (weight G S.palette) (weight G _) (copy G S.palette torsion b.signature b.retained b.proper)
    (fun q => congrArg (fun t : TreeOccurrence (OI.K G) => t.1.1)
      (GeneratedOccurrenceWorklistPartition.copyId_leaf G S.palette torsion b.signature b.retained b.proper q))
    S.todo o pending _ (S.higherDisjoint G base o b torsion)
  intro q hq
  have hl := GeneratedOccurrenceWorklistPartition.newIds_lower G S.palette torsion b.signature b.retained b.proper q hq
  have he : b.m+2 = weight G S.palette o := congrArg Sigma.fst b.literal
  change weight G _ q < weight G S.palette o
  rw [← he]
  exact hl

def Earlier (T S : State G base) : Prop := Multiset.IsDershowitzMannaLT (T.rank G base) (S.rank G base)

theorem earlier_wellFounded : WellFounded (Earlier G base) :=
  InvImage.wf (fun S : State G base => S.rank G base) Multiset.wellFounded_isDershowitzMannaLT

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedOccurrenceWorklist
