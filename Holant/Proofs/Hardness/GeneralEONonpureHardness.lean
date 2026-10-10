import Holant.Proofs.Hardness.GeneralEOCommonSignSelection
import Holant.Proofs.Hardness.GeneralEOSelectedFilterSource
import Holant.Proofs.Hardness.GeneralEODEQProducedSource
import Holant.Proofs.Hardness.GeneralEOClosedHardness
import Holant.Proofs.Hardness.GeneralEONonpurePinning

/-! Common-sign nonpure negative EO hardness. Two independently selected
failed restrictions are implemented by physical filters using the internally
produced DEQ4. The universal closed-support source, finite field retraction,
filter substitution, scaled DEQ removal, and pin removal compose literally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonpureHardness
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace S
export GeneralEOCommonSignSelection (Choice choose indices arity bounded originals pairings family
  central nonzero closed compressed_failures)
end S
namespace D
export GeneralEODEQProducedSource (network labels selectedScalar tables arity signatures new_signature
  native_tables pinnedSource)
end D
namespace P
export GeneralEOPinnedDescentPalette (oldLabel original original_value pinned presentation pinnedTables pinnedValue)
end P
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end O
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (sign : EOSign) (he : ∀i,Signature.CentralSupport (G i))
variable (hs : ∀i,EONegativeWitness.Supports sign (EONegativePairReduction.signature G i))
variable (negative : ¬EOTract (preprocess (EONegativePairReduction.family G)))
variable (j : Fin s) (hp : ¬GeneralEODEQProducer.Pure sign (G j))
local instance : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'
variable (c : S.Choice G)

def originalLabel (i : Fin 2) : Fin s := ⟨S.indices G c i.val,S.bounded G c i⟩
def rows (i : Fin 2) : Signature (O.originalField G) (S.arity G c i.val) :=
  P.original G (originalLabel G c i)
def targetLabel (i : Fin 2) : Fin (s+1+1) :=
  ⟨(originalLabel G c i).val,Nat.lt_trans (originalLabel G c i).isLt (by omega)⟩

theorem rows_value (i : Fin 2) (x : Fin (S.arity G c i.val) → Bool) :
    (rows G c i x : AlgebraicComplex)=S.originals G c i x := rfl

theorem target_slot (i : Fin 2) :
    (⟨D.arity G j sign (he j) (hs j) hp (targetLabel G c i).val,
      D.signatures G j sign (he j) (hs j) hp (targetLabel G c i)⟩ : AnySignature (O.originalField G))=
      ⟨S.arity G c i.val,rows G c i⟩ := by
  have h := GeneralEODEQActualAdjoin.old_signature (P.presentation G) (P.pinnedTables G)
    (D.network G j sign (he j) (hs j) hp) (D.labels G j sign (he j) (hs j) hp)
    (D.selectedScalar G j sign (he j) (hs j) hp) (P.oldLabel (originalLabel G c i))
  have hf : GeneralEODEQPairingTemplates.family (P.presentation G) (P.pinnedTables G)=P.pinned G := by
    funext k x
    exact (P.presentation G).decode.apply_symm_apply _
  rw [hf] at h
  exact h.trans (GeneralEOPinnedDescentPalette.palette_old (P.original G) (originalLabel G c i))

/-- Each of the two selected restrictions has its own actual graph. The
source labels remain distinct even when their original target labels coincide. -/
def filterSource : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding 2 1 (S.arity G c)) (O.originalPresentation (S.family G c)).encoding
    (GeneralEODEQProducedSource.inputEncoding G j sign (he j) (hs j) hp) (P.presentation G).encoding
    (O.originalValue (S.family G c)) (GeneralEODEQProducedSource.value G j sign (he j) (hs j) hp) :=
  GeneralEOSelectedFilterSource.source (O.originalField G) (P.presentation G)
    (D.tables G j sign (he j) (hs j) hp) (rows G c) (S.originals G c) (S.pairings G c)
    (targetLabel G c) (target_slot G sign he hs j hp c) ⟨s+1,Nat.lt_succ_self (s+1)⟩
    (D.new_signature G j sign (he j) (hs j) hp) (D.native_tables G j sign (he j) (hs j) hp)
    (rows_value G c)

variable {α : Type} {ea : Encoding α Bool} {count : α → ℕ}

/-- Universal all-arity closed-support hardness is fed the actual internally
selected two-row family, retaining both independently failed class choices. -/
def selectedSource (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding 2 1 (S.arity G c)) (O.originalPresentation (S.family G c)).encoding
    count (O.originalValue (S.family G c)) :=
  GeneralEOClosedHardness.source (S.family G c) (S.central G he c) (S.nonzero G c)
    (S.closed G sign hs c) (S.compressed_failures G sign he hs c).1
    (S.compressed_failures G sign he hs c).2 w

/-- Only original G labels and the directed pin remain after composing the
actual restricted-family source, filter graphs, and produced DEQ removal. -/
def pinnedSource (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding (s+1) 1 (GeneralEOPinnedDescentPalette.arity (s:=s) (a:=a)))
    (P.presentation G).encoding count (P.pinnedValue G) :=
  C.composeControlled (selectedSource G sign he hs (S.choose G sign he hs negative) w)
    (C.composeControlled (filterSource G sign he hs j hp (S.choose G sign he hs negative))
      (D.pinnedSource G j sign (he j) (hs j) hp))

/-- An actual pin eliminator removes the final pin using the unchanged
original target function, incidence encoding, and answer presentation. -/
def originalSource (eliminate : GeneralEOPinEliminationCases.Elimination G)
    (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  C.composeControlled (pinnedSource G sign he hs negative j hp w) eliminate

include he hs negative hp in
theorem original_countingHard (eliminate : GeneralEOPinEliminationCases.Elimination G) :
    Holant.LocalDrafts.CountingHardness.WitnessCountingHard (RawClosedNetwork.validatedEncoding s 1 a)
      (O.originalPresentation G).encoding (O.originalValue G) := by
  intro α ea f w
  exact ⟨(originalSource G sign he hs negative j hp eliminate w).reduction⟩

include he hs negative hp in
/-- Final nonpure common-sign branch: the original row itself supplies the
pinning-or-hardness split. No non-ARS, pin, DEQ, gadget or backend premise remains. -/
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (O.originalValue G) := by
  rcases GeneralEONonpurePinning.pinning_or_hardness G j sign (he j) (hs j) hp with h | h
  · exact original_countingHard G sign he hs negative j hp (Classical.choice h)
  · exact h

/-- An actual oracle programme on the unchanged original family, selected
from the internally established branch. -/
def source (w : SharpPWitness ea count) : PolyTimeOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    count (O.originalValue G) :=
  Classical.choice (countingHard G sign he hs negative j hp α ea count w)

variable (nonpure : ¬∀i,GeneralEODEQProducer.Pure sign (G i))

include he hs negative nonpure in
/-- The nonpure original label is selected internally as well. -/
theorem exists_nonpure_countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation G).encoding
    (O.originalValue G) := by
  classical
  obtain ⟨i,hi⟩ := not_forall.mp nonpure
  exact countingHard G sign he hs negative i hi

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONonpureHardness
