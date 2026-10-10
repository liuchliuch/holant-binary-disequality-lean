import Holant.Proofs.Closure.RetainedSingle
import Holant.Proofs.Closure.DeckAddressAccess

/-! Reconstructed separately charged access to the regenerated CURRENT deck
and exact saved addresses, including the standalone zero. UNVERIFIED recovery. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

structure CurrentSignatureAccess (q : AnySignature (OI.K G)) where
  power : GeneralPowerExposure.PowerMacro P.table q.2
  toOriginal : RetainedBranch.ToOriginalProgramme G P q
  fromOriginal : RetainedBranch.FromOriginalProgramme G P q
  samePower : toOriginal.controlled.reduction.machine =
    (RetainedBranch.controlledToOriginal G P q power).reduction.machine
  sameReverse : fromOriginal.controlled.reduction.machine =
    (RetainedBranch.controlledFromOriginal G P q).reduction.machine

def currentSignatureAccess (q : AnySignature (OI.K G)) (actual : Gadget.Realizes P.family .disequality q.2) :
    CurrentSignatureAccess G P q :=
  let M := DeckDirect.directPower P.table (P.retainsIdentity G) actual
  ⟨M,RetainedBranch.toOriginal G P q M,RetainedBranch.fromOriginal G P q,rfl,rfl⟩

abbrev CurrentSubtreeAccess (u : TreeOccurrence (OI.K G)) := CurrentSignatureAccess G P u.1

variable (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)

def currentSubtreeAccess (k : FullDeckIndex P.family torsion f) (u : TreeOccurrence (OI.K G))
    (hu : OccurrenceSchedule.StoredSubtree u (fullDeckRoot P.family torsion f k)) : CurrentSubtreeAccess G P u :=
  let M := deckSubtreePower G P torsion f core hcore k u hu
  ⟨M,RetainedBranch.subtreeToOriginal G P torsion f core hcore k u hu,
    RetainedBranch.subtreeFromOriginal G P u,rfl,rfl⟩

def currentAddressAccess (k : FullDeckIndex P.family torsion f) (path : List Bool)
    (u : TreeOccurrence (OI.K G)) (hu : QueueTagged.lookupTree (fullDeckRoot P.family torsion f k) path = some u) :
    CurrentSubtreeAccess G P u :=
  let M := DeckAddressAccess.deckAddressPower G P torsion f core hcore k path u hu
  ⟨M,DeckAddressAccess.addressToOriginal G P torsion f core hcore k path u hu,
    DeckAddressAccess.addressFromOriginal G P u,rfl,rfl⟩

structure RegeneratedDeckAccess where
  raw : ∀ k : RawCardKey m (completeGroup P.family torsion), DeckDirect P.family (rawCard P.family torsion f k)
  entireRawDeck : ∀ g : Signature (OI.K G) m, g ∈ rawDeck P.family torsion f → DeckDirect P.family g
  rawProgramme : ∀ g : Signature (OI.K G) m, g ∈ rawDeck P.family torsion f → CurrentSignatureAccess G P ⟨m,g⟩
  roots : ∀ k : FullDeckIndex P.family torsion f, DeckDirect P.family (fullDeckRoot P.family torsion f k).1.2
  subtree : ∀ k : FullDeckIndex P.family torsion f, ∀ u : TreeOccurrence (OI.K G),
    OccurrenceSchedule.StoredSubtree u (fullDeckRoot P.family torsion f k) → CurrentSubtreeAccess G P u
  address : ∀ k : FullDeckIndex P.family torsion f, ∀ path : List Bool, ∀ u : TreeOccurrence (OI.K G),
    QueueTagged.lookupTree (fullDeckRoot P.family torsion f k) path = some u → CurrentSubtreeAccess G P u
  rawCoverage : ∀ g ∈ rawDeck P.family torsion f, g=0 ∨ ∃ k : FullDeckIndex P.family torsion f,
    (fullDeckRoot P.family torsion f k).1 = (⟨m,g⟩ : AnySignature (OI.K G))

def regeneratedDeckAccess : RegeneratedDeckAccess G P torsion f where
  raw := deckRawDirect G P torsion f core hcore
  entireRawDeck := deckRawDeckDirect G P torsion f core hcore
  rawProgramme g hg := currentSignatureAccess G P ⟨m,g⟩ (deckRawDeckDirect G P torsion f core hcore g hg).realizes
  roots := deckRootDirect G P torsion f core hcore
  subtree := currentSubtreeAccess G P torsion f core hcore
  address := currentAddressAccess G P torsion f core hcore
  rawCoverage := deckRawCoverage G P torsion f

theorem regenerated_zero_key (k : RawCardKey m (completeGroup P.family torsion))
    (hz : rawCard P.family torsion f k = 0) :
    ((regeneratedDeckAccess G P torsion f core hcore).raw k).network.denote = 0 :=
  ((regeneratedDeckAccess G P torsion f core hcore).raw k).value.trans hz

def regeneratedRootAccess (k : FullDeckIndex P.family torsion f) :
    CurrentSubtreeAccess G P (fullDeckRoot P.family torsion f k) :=
  currentAddressAccess G P torsion f core hcore k [] (fullDeckRoot P.family torsion f k) rfl

@[simp] theorem regenerated_same_machine (k : FullDeckIndex P.family torsion f) :
    (regeneratedRootAccess G P torsion f core hcore k).toOriginal.controlled.reduction.machine =
      (RetainedBranch.controlledToOriginal G P _ (regeneratedRootAccess G P torsion f core hcore k).power).reduction.machine := rfl

@[simp] theorem currentSignatureAccess_controlled (q : AnySignature (OI.K G))
    (actual : Gadget.Realizes P.family .disequality q.2) :
    (currentSignatureAccess G P q actual).toOriginal.controlled =
      RetainedBranch.controlledToOriginal G P q (currentSignatureAccess G P q actual).power := rfl
@[simp] theorem currentSubtreeAccess_controlled (k : FullDeckIndex P.family torsion f) (u : TreeOccurrence (OI.K G))
    (hu : OccurrenceSchedule.StoredSubtree u (fullDeckRoot P.family torsion f k)) :
    (currentSubtreeAccess G P torsion f core hcore k u hu).toOriginal.controlled =
      RetainedBranch.controlledToOriginal G P u.1 (currentSubtreeAccess G P torsion f core hcore k u hu).power := rfl
@[simp] theorem currentAddressAccess_controlled (k : FullDeckIndex P.family torsion f) (path : List Bool)
    (u : TreeOccurrence (OI.K G)) (hu : QueueTagged.lookupTree (fullDeckRoot P.family torsion f k) path = some u) :
    (currentAddressAccess G P torsion f core hcore k path u hu).toOriginal.controlled =
      RetainedBranch.controlledToOriginal G P u.1 (currentAddressAccess G P torsion f core hcore k path u hu).power := rfl

namespace RetainedFinalAccess

def Access (E : StructuralExit G P) : Type 1 :=
  match E with
  | .unary u _ _ => CurrentSignatureAccess G P ⟨1,u⟩
  | .infinite B _ _ => CurrentSignatureAccess G P ⟨2,binarySignature B⟩
  | .odd q _ _ _ _ => CurrentSignatureAccess G P q
  | .stable _ f _ _ torsion _ _ _ _ _ => RegeneratedDeckAccess G P torsion f

def forStructuralExit (E : StructuralExit G P) : Access G P E :=
  match E with
  | .unary u retained _ => currentSignatureAccess G P ⟨1,u⟩ (Gadget.realizes_of_mem P.family .disequality u retained)
  | .infinite B actual _ => currentSignatureAccess G P ⟨2,binarySignature B⟩ actual.1
  | .odd q retained _ _ _ => currentSignatureAccess G P q (Gadget.realizes_of_mem P.family .disequality q.2 retained)
  | .stable _ f _ _ torsion minimum core _ _ _ => regeneratedDeckAccess G P torsion f minimum core

end RetainedFinalAccess
end Holant.LocalDrafts.RemoteWork.StableClosureV2
