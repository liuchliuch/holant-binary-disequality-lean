import Holant.Proofs.Closure.DeckLocation
import Holant.Proofs.Closure.RetainedSingle
import Holant.Proofs.Closure.RetainedCatalogue

/-! Reconstructed canonical-address macros and charged physical programmes.
The located slot is the one inspected by the queue. UNVERIFIED recovery. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.DeckAddressAccess
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)

def deckAddressPower (k : FullDeckIndex P.family torsion f) (path : List Bool)
    (u : TreeOccurrence (OI.K G)) (h : QueueTagged.lookupTree (fullDeckRoot P.family torsion f k) path = some u) :
    GeneralPowerExposure.PowerMacro P.table u.1.2 :=
  locatedData (fullDeckRoot P.family torsion f k) path u h
    (fun z => GeneralPowerExposure.PowerMacro P.table z.1.2)
    (deckSlotPower G P torsion f core hcore k)

@[simp] theorem deckAddressPower_at_slot (k : FullDeckIndex P.family torsion f)
    (j : FactorSaturation.Slots (fullDeckRoot P.family torsion f k).2) :
    deckAddressPower G P torsion f core hcore k
      (FactorSaturation.path (fullDeckRoot P.family torsion f k).2 j)
      (FactorSaturation.slot (fullDeckRoot P.family torsion f k).2 j) (lookupTree_slot _ j) =
      deckSlotPower G P torsion f core hcore k j :=
  locatedData_at_slot _ j _ _

@[simp] theorem deckAddressPower_at_leaf (k : FullDeckIndex P.family torsion f)
    (j : FactorSaturation.Leaves (fullDeckRoot P.family torsion f k).2) :
    deckAddressPower G P torsion f core hcore k (savedLeafPath (fullDeckRoot P.family torsion f k).2 j)
      (FactorSaturation.slot (fullDeckRoot P.family torsion f k).2 (FactorSaturation.leafSlot _ j))
      (lookupTree_slot _ (FactorSaturation.leafSlot _ j)) =
      deckSlotPower G P torsion f core hcore k (FactorSaturation.leafSlot _ j) :=
  deckAddressPower_at_slot G P torsion f core hcore k _

theorem addressMacro_installed_leaf (k : FullDeckIndex P.family torsion f)
    (j : FactorSaturation.Leaves (fullDeckRoot P.family torsion f k).2) :
    deckAddressPower G P torsion f core hcore k (savedLeafPath (fullDeckRoot P.family torsion f k).2 j)
      (FactorSaturation.slot (fullDeckRoot P.family torsion f k).2 (FactorSaturation.leafSlot _ j))
      (lookupTree_slot _ (FactorSaturation.leafSlot _ j)) =
      RetainedCatalogue.newIndexPower G P torsion f core hcore (.inr ⟨k,j⟩) :=
  (deckAddressPower_at_leaf G P torsion f core hcore k j).trans
    (RetainedCatalogue.newIndexPower_leaf G P torsion f core hcore k j).symm

def addressToOriginal (k : FullDeckIndex P.family torsion f) (path : List Bool)
    (u : TreeOccurrence (OI.K G)) (h : QueueTagged.lookupTree (fullDeckRoot P.family torsion f k) path = some u) :
    RetainedBranch.ToOriginalProgramme G P u.1 :=
  RetainedBranch.toOriginal G P u.1 (deckAddressPower G P torsion f core hcore k path u h)

def addressFromOriginal (u : TreeOccurrence (OI.K G)) : RetainedBranch.FromOriginalProgramme G P u.1 :=
  RetainedBranch.fromOriginal G P u.1

@[simp] theorem address_same_machine (k : FullDeckIndex P.family torsion f) (path : List Bool)
    (u : TreeOccurrence (OI.K G)) (h : QueueTagged.lookupTree (fullDeckRoot P.family torsion f k) path = some u) :
    (addressToOriginal G P torsion f core hcore k path u h).controlled.reduction.machine =
      (RetainedBranch.controlledToOriginal G P u.1 (deckAddressPower G P torsion f core hcore k path u h)).reduction.machine := rfl
@[simp] theorem address_same_controlled (k : FullDeckIndex P.family torsion f) (path : List Bool)
    (u : TreeOccurrence (OI.K G)) (h : QueueTagged.lookupTree (fullDeckRoot P.family torsion f k) path = some u) :
    (addressToOriginal G P torsion f core hcore k path u h).controlled =
      RetainedBranch.controlledToOriginal G P u.1 (deckAddressPower G P torsion f core hcore k path u h) := rfl
@[simp] theorem address_same_clock (k : FullDeckIndex P.family torsion f) (path : List Bool)
    (u : TreeOccurrence (OI.K G)) (h : QueueTagged.lookupTree (fullDeckRoot P.family torsion f k) path = some u) :
    (addressToOriginal G P torsion f core hcore k path u h).controlled.reduction.time =
      (RetainedBranch.controlledToOriginal G P u.1 (deckAddressPower G P torsion f core hcore k path u h)).reduction.time := rfl

theorem addressToOriginal_at_slot (k : FullDeckIndex P.family torsion f)
    (j : FactorSaturation.Slots (fullDeckRoot P.family torsion f k).2) :
    addressToOriginal G P torsion f core hcore k (FactorSaturation.path _ j)
      (FactorSaturation.slot _ j) (lookupTree_slot _ j) =
      RetainedBranch.slotToOriginal G P torsion f core hcore k j := by
  unfold addressToOriginal RetainedBranch.slotToOriginal
  rw [deckAddressPower_at_slot]

theorem addressProgramme_installed_leaf (k : FullDeckIndex P.family torsion f)
    (j : FactorSaturation.Leaves (fullDeckRoot P.family torsion f k).2) :
    addressToOriginal G P torsion f core hcore k (savedLeafPath _ j)
      (FactorSaturation.slot _ (FactorSaturation.leafSlot _ j)) (lookupTree_slot _ (FactorSaturation.leafSlot _ j)) =
      RetainedBranch.toOriginal G P (RetainedCatalogue.newOccurrence G P torsion f (.inr ⟨k,j⟩)).1
        (RetainedCatalogue.newIndexPower G P torsion f core hcore (.inr ⟨k,j⟩)) := by
  unfold addressToOriginal
  rw [addressMacro_installed_leaf]
  rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.DeckAddressAccess
