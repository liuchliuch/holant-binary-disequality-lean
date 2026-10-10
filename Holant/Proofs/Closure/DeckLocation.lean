import Holant.Proofs.Closure.DeckKernel
import Holant.Proofs.Closure.QueueTaggedLookup

/-! Data-valued lookup of an exact canonical stored address. The slot is
computed by tree/path recursion, never by existential subtree re-selection. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.DeckAddressAccess
open Holant
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness
variable {L : Type} [Field L]

def locatedSlot (root : TreeOccurrence L) (p : List Bool) :
    (u : TreeOccurrence L) → QueueTagged.lookupTree root p = some u → FactorSaturation.Slots root.2 :=
  match p with
  | [] => fun _ _ => savedRootSlot root.2
  | b::p => match root with
    | ⟨_,.leaf _ _⟩ => fun _ h => False.elim (by cases h)
    | ⟨_,.split sp l r⟩ => match b with
      | false => fun u h => Sum.inr (Sum.inl (locatedSlot ⟨_,l⟩ p u h))
      | true => fun u h => Sum.inr (Sum.inr (locatedSlot ⟨_,r⟩ p u h))

theorem locatedSlot_path (root : TreeOccurrence L) (p : List Bool) (u : TreeOccurrence L)
    (h : QueueTagged.lookupTree root p = some u) :
    FactorSaturation.path root.2 (locatedSlot root p u h) = p := by
  induction p generalizing root with
  | nil =>
    obtain ⟨r,t⟩ := root
    cases t <;> rfl
  | cons b p ih =>
    obtain ⟨r,t⟩ := root
    cases t with
    | leaf => cases h
    | split sp l r =>
      cases b with
      | false => exact congrArg (List.cons false) (ih ⟨_,l⟩ h)
      | true => exact congrArg (List.cons true) (ih ⟨_,r⟩ h)

theorem locatedSlot_value (root : TreeOccurrence L) (p : List Bool) (u : TreeOccurrence L)
    (h : QueueTagged.lookupTree root p = some u) :
    FactorSaturation.slot root.2 (locatedSlot root p u h) = u := by
  induction p generalizing root with
  | nil =>
    have he : root = u := Option.some.inj h
    exact (savedRootSlot_value root.2).trans he
  | cons b p ih =>
    obtain ⟨r,t⟩ := root
    cases t with
    | leaf => cases h
    | split sp l r =>
      cases b with
      | false => exact ih ⟨_,l⟩ h
      | true => exact ih ⟨_,r⟩ h


/-- Every explicit saved slot is found at its canonical address. -/
theorem lookupTree_slot {r : AnySignature L} (t : FactorTree r) (j : FactorSaturation.Slots t) :
    QueueTagged.lookupTree (⟨r,t⟩ : TreeOccurrence L) (FactorSaturation.path t j) =
      some (FactorSaturation.slot t j) := by
  induction t with
  | leaf => rfl
  | split sp l rr il ir =>
    rcases j with _ | (j | j)
    · rfl
    · exact il j
    · exact ir j

/-- Locator inversion is data identity, even for equal tables at different
paths. This binds indexed catalogue macros to actual inspected addresses. -/
theorem locatedSlot_at_slot {r : AnySignature L} (t : FactorTree r) (j : FactorSaturation.Slots t)
    (h : QueueTagged.lookupTree (⟨r,t⟩ : TreeOccurrence L) (FactorSaturation.path t j) =
      some (FactorSaturation.slot t j)) :
    locatedSlot ⟨r,t⟩ (FactorSaturation.path t j) (FactorSaturation.slot t j) h = j :=
  FactorSaturation.path_injective t (locatedSlot_path _ _ _ h)


/-- Transport data from the uniquely computed saved slot to its full exact
occurrence. This is the only type transport used by addressed programmes. -/
def locatedData (root : TreeOccurrence L) (p : List Bool) (u : TreeOccurrence L)
    (h : QueueTagged.lookupTree root p = some u) (C : TreeOccurrence L → Type)
    (data : ∀ j : FactorSaturation.Slots root.2, C (FactorSaturation.slot root.2 j)) : C u :=
  (locatedSlot_value root p u h) ▸ data (locatedSlot root p u h)


theorem transport_data_pair {α : Type} {C : α → Type} {u v : α}
    (h : u=v) (data : C u) : (⟨v,h ▸ data⟩ : Sigma C) = ⟨u,data⟩ := by
  cases h
  rfl

theorem locatedData_at_slot {r : AnySignature L} (t : FactorTree r) (j : FactorSaturation.Slots t)
    (C : TreeOccurrence L → Type) (data : ∀ j : FactorSaturation.Slots t, C (FactorSaturation.slot t j)) :
    locatedData ⟨r,t⟩ (FactorSaturation.path t j) (FactorSaturation.slot t j)
      (lookupTree_slot t j) C data = data j := by
  let h := lookupTree_slot t j
  have hp := transport_data_pair (locatedSlot_value ⟨r,t⟩ (FactorSaturation.path t j)
    (FactorSaturation.slot t j) h)
    (data (locatedSlot ⟨r,t⟩ (FactorSaturation.path t j) (FactorSaturation.slot t j) h))
  have hj := congrArg (fun z => (⟨FactorSaturation.slot t z,data z⟩ : Sigma C))
    (locatedSlot_at_slot t j h)
  exact eq_of_heq (Sigma.mk.inj_iff.mp (hp.trans hj)).2

structure Located (root : TreeOccurrence L) (p : List Bool) (u : TreeOccurrence L) where
  slot : FactorSaturation.Slots root.2
  path : FactorSaturation.path root.2 slot = p
  value : FactorSaturation.slot root.2 slot = u

def locate (root : TreeOccurrence L) (p : List Bool) (u : TreeOccurrence L)
    (h : QueueTagged.lookupTree root p = some u) : Located root p u :=
  ⟨locatedSlot root p u h,locatedSlot_path root p u h,locatedSlot_value root p u h⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.DeckAddressAccess
