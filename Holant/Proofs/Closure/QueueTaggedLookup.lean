import Holant.Proofs.FiniteGroups.Stabilization.OccurrenceSchedule.Stored

/-! Reconstructed canonical addressed lookup. A lookup follows only the actual
saved constructors at its exact Boolean branch address. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueTagged
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule
variable {L : Type*} [Field L]

abbrev Item (L : Type*) [Field L] := List Bool × TreeOccurrence L

def lookupTree (root : TreeOccurrence L) (p : List Bool) : Option (TreeOccurrence L) :=
  match p with
  | [] => some root
  | b::p => match root with
    | ⟨_,.leaf _ _⟩ => none
    | ⟨_,.split sp l r⟩ => match b with
      | false => lookupTree ⟨_,l⟩ p
      | true => lookupTree ⟨_,r⟩ p

@[simp] theorem lookupTree_nil (root : TreeOccurrence L) : lookupTree root [] = some root := rfl

theorem lookupTree_append (root : TreeOccurrence L) (p q : List Bool) :
    lookupTree root (p ++ q) = (lookupTree root p).bind (fun u => lookupTree u q) := by
  induction p generalizing root with
  | nil => rfl
  | cons b p ih =>
    obtain ⟨f,t⟩ := root
    cases t with
    | leaf => rfl
    | split sp l r =>
      cases b with
      | false => exact ih ⟨_,l⟩
      | true => exact ih ⟨_,r⟩

theorem lookupTree_append_of_some (root : TreeOccurrence L) (p q : List Bool)
    (u : TreeOccurrence L) (h : lookupTree root p = some u) :
    lookupTree root (p ++ q) = lookupTree u q := by
  rw [lookupTree_append,h]
  rfl

theorem lookupTree_stored (root : TreeOccurrence L) (p : List Bool) (u : TreeOccurrence L)
    (h : lookupTree root p = some u) : StoredSubtree u root := by
  induction p generalizing root with
  | nil =>
    have he : root = u := Option.some.inj h
    rw [←he]
    exact .root root
  | cons b p ih =>
    obtain ⟨f,t⟩ := root
    cases t with
    | leaf => cases h
    | split sp l r =>
      cases b with
      | false => exact .left sp l r (ih ⟨_,l⟩ h)
      | true => exact .right sp l r (ih ⟨_,r⟩ h)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.QueueTagged
