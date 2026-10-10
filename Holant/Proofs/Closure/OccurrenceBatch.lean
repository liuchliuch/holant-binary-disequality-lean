import Holant.Proofs.Closure.QueueDeck
import Holant.Proofs.Closure.ProgrammeRetained

/-! Physical full-deck batches for arbitrary retained occurrences.
No minimum-core premise is needed for this additive producer. It prepares
higher-arity occurrences without falsely treating them as a rank descent.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceBatch
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.Certificates.MatchingContractionClosure
open RetainedCatalogue
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family)

/-- Actual power macro for the exact stored slot of this retained occurrence. -/
def slotPower (k : FullDeckIndex P.family torsion f)
    (j : FactorSaturation.Slots (fullDeckRoot P.family torsion f k).2) :
    GeneralPowerExposure.PowerMacro P.table
      (FactorSaturation.slot (fullDeckRoot P.family torsion f k).2 j).1.2 := by
  have hr := fullDeckRoot_realizes P.family torsion (P.retainsIdentity G) (by norm_num) f
    (Gadget.realizes_of_mem P.family .disequality f retained) k
  cases savedSlotSplit (fullDeckRoot P.family torsion f k).2 j with
  | root he =>
    rw [← he]
    exact DeckDirect.directPower P.table (P.retainsIdentity G) hr
  | factor b split =>
    exact Classical.choice (split.left_power_labelled P.table (P.retainsIdentity G)
      (by norm_num) (mixedSupport_of_identity P.family (P.retainsIdentity G))
      (fullDeckRoot_nonzero P.family torsion f k) hr)

def indexPower : (x : NewIndex G P torsion f) →
    GeneralPowerExposure.PowerMacro P.table (newOccurrence G P torsion f x).1.2 := by
  intro x
  cases x with
  | inl k =>
    exact DeckDirect.directPower P.table (P.retainsIdentity G)
      (fullDeckRoot_realizes P.family torsion (P.retainsIdentity G) (by norm_num) f
        (Gadget.realizes_of_mem P.family .disequality f retained) k)
  | inr x =>
    exact slotPower G P torsion f retained x.1
      (FactorSaturation.leafSlot (Root G P torsion f x.1).2 x.2)

def densePower (j : Fin (addedCount G P torsion f)) :
    GeneralPowerExposure.PowerMacro (original G P torsion f) (T G P torsion f (P.count+j.val)) := by
  change GeneralPowerExposure.PowerMacro (original G P torsion f)
    (lookup G P torsion f (P.count+j.val)).2
  rw [lookup_new]
  exact relabelPower G P torsion f (indexPower G P torsion f retained (enumerate G P torsion f j))

def chain : RecursiveMachine.Chain (original G P torsion f) (table G P torsion f) :=
  FactorSaturation.PrefixMachine.chain (T G P torsion f)
    (densePower G P torsion f retained) (addedCount G P torsion f) le_rfl

/-- The new alphabet's compiler is constructed from actual macros, not an input. -/
def controlledToOriginal : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (count G P torsion f) 1 (arity G P torsion f))
    (OI.presentation G).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    (OriginalLCodec.value (table G P torsion f)) (OriginalForestSource.value G) :=
  InitialProgrammes.withTerminal (OI.presentation G)
    (Programme.compose (toOld G P torsion f) P.toOriginal.controlled)
    (chain G P torsion f retained)

def palette (hm : 2 ≤ m) : Palette G :=
  withPhysical G P torsion f hm
    (PhysicalProgramme.ofControlled (controlledToOriginal G P torsion f retained))
    (PhysicalProgramme.ofControlled (ProgrammeRetained.controlledFromOriginal G P torsion f))

@[simp] theorem family_exact (hm : 2 ≤ m) :
    (palette G P torsion f retained hm).family = fullRetainedDeck P.family torsion f :=
  RetainedCatalogue.family_exact G P torsion f

def result (hm : 2 ≤ m) : DeckBatchResult G P torsion f where
  palette := palette G P torsion f retained hm
  oldSaved i := ⟨oldLabel G P torsion f i,old_saved G P torsion f i⟩
  deckSaved k := ⟨deckLabel G P torsion f k,deck_saved G P torsion f k⟩
  finalQueue := FullQueue.finalQueue G P torsion f
  queueRun := FullQueue.initial_to_final G P torsion f
  exhausted := FullQueue.exhausted G P torsion f
  allDone := FullQueue.allDone G P torsion f

/-- Preparation of any retained even-arity occurrence, irrespective of smaller
retained cores. This is not a global termination or rigidity conclusion. -/
theorem complete_retained_occurrence_batch
    (hf : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family) (hm : 2 ≤ m) :
    Nonempty (DeckBatchResult G P torsion f) := ⟨result G P torsion f hf hm⟩

@[simp] theorem toOriginal_same_machine (hm : 2 ≤ m) :
    (palette G P torsion f retained hm).toOriginal.controlled.reduction.machine =
      (controlledToOriginal G P torsion f retained).reduction.machine := rfl

@[simp] theorem fromOriginal_same_machine (hm : 2 ≤ m) :
    (palette G P torsion f retained hm).fromOriginal.controlled.reduction.machine =
      (ProgrammeRetained.controlledFromOriginal G P torsion f).reduction.machine := rfl

end Holant.LocalDrafts.RemoteWork.StableClosureV2.OccurrenceBatch
