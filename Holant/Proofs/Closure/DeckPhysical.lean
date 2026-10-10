import Holant.Proofs.Closure.Interface
import Holant.Proofs.Closure.DeckKernel

/-! Literal raw-key gadgets and actual saved-tree factor-power provenance.
All constructions retain the original coefficient field. Zero raw cards have
ordinary direct graphs too; only nonzero cards enter the retained catalogue. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.OpenNetworkComposition
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.Certificates.MatchingContractionClosure

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

namespace Palette

theorem retainsIdentity (P : Palette G) : RetainsIdentity P.family := P.equality

theorem finite (P : Palette G) : P.family.Finite := Set.finite_range _

theorem saturated (P : Palette G) : FactorSaturated P.family := by
  rintro f ⟨i, rfl⟩ _
  exact ⟨P.trees i, P.leavesRetained i⟩

end Palette


variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))

/-- Every literal key has its own actual direct graph, even when its card is
zero or shares a projective key with a different nonzero card. -/
def deckRawDirect (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (k : RawCardKey m (completeGroup P.family torsion)) :
    DeckDirect P.family (rawCard P.family torsion f k) := by
  have hf : Gadget.Realizes P.family .disequality f := by
    apply Gadget.realizes_of_mem
    simpa only [hcore] using core.retained
  exact DeckDirect.ofRealizes (P.retainsIdentity G)
    (rawCard_realizes_exact P.family torsion (P.retainsIdentity G) (by norm_num) f hf k)


/-- Physical zero sentinel: an actual one-copy card graph tensored with the
literal-I/native-X closed zero component, all over the current source P. -/
def deckZeroDirect (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩) :
    DeckDirect P.family (0 : Signature (OI.K G) m) := by
  let k : RawCardKey m (completeGroup P.family torsion) :=
    (fun _ => none,Equiv.refl _,1,false)
  have hf : Gadget.Realizes P.family .disequality f :=
    Gadget.realizes_of_mem P.family .disequality f (by simpa only [hcore] using core.retained)
  exact DeckDirect.zeroFrom (P.retainsIdentity G)
    (rawCard_realizes_exact P.family torsion (P.retainsIdentity G) (by norm_num) f hf k)

/-- Entire literal rawDeck direct coverage, including its standalone zero
sentinel as well as every actual zero/nonzero raw-card key. -/
def deckRawDeckDirect (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (g : Signature (OI.K G) m) (hg : g ∈ rawDeck P.family torsion f) : DeckDirect P.family g := by
  classical
  by_cases hz : g = 0
  · subst g
    exact deckZeroDirect G P torsion f core hcore
  · have hk : ∃ k : RawCardKey m (completeGroup P.family torsion), rawCard P.family torsion f k = g := by
      rcases hg with hg | hg
      · exact False.elim (hz hg)
      · exact hg
    have he := Classical.choose_spec hk
    rw [← he]
    exact deckRawDirect G P torsion f core hcore (Classical.choose hk)

/-- This same saved root occurrence has an ordinary source-labelled graph. -/
def deckRootDirect (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (k : FullDeckIndex P.family torsion f) :
    DeckDirect P.family (fullDeckRoot P.family torsion f k).1.2 := by
  apply DeckDirect.ofRealizes (P.retainsIdentity G)
  apply fullDeckRoot_realizes P.family torsion (P.retainsIdentity G) (by norm_num) f
  · apply Gadget.realizes_of_mem
    simpa only [hcore] using core.retained

/-- Complete raw coverage includes the distinguished zero and every zero key,
while a nonzero key retains its literal unnormalized full root occurrence. -/
theorem deckRawCoverage (g : Signature (OI.K G) m) (hg : g ∈ rawDeck P.family torsion f) :
    g = 0 ∨ ∃ k : FullDeckIndex P.family torsion f,
      (fullDeckRoot P.family torsion f k).1 = (⟨m,g⟩ : AnySignature (OI.K G)) := by
  classical
  rcases hg with rfl | ⟨k, rfl⟩
  · exact Or.inl rfl
  · by_cases hk : rawCard P.family torsion f k = 0
    · exact Or.inl hk
    · exact Or.inr ⟨.inr ⟨k,hk⟩, rfl⟩

/-- Actual source macro for one explicitly indexed saved subtree. Its
flattened split is constructed by inspecting that same FactorTree. -/
def deckSlotPower (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (k : FullDeckIndex P.family torsion f)
    (j : FactorSaturation.Slots (fullDeckRoot P.family torsion f k).2) :
    GeneralPowerExposure.PowerMacro P.table
      (FactorSaturation.slot (fullDeckRoot P.family torsion f k).2 j).1.2 := by
  have hr := fullDeckRoot_realizes P.family torsion (P.retainsIdentity G) (by norm_num) f
    (Gadget.realizes_of_mem P.family .disequality f (by simpa only [hcore] using core.retained)) k
  cases savedSlotSplit (fullDeckRoot P.family torsion f k).2 j with
  | root he =>
    rw [← he]
    exact DeckDirect.directPower P.table (P.retainsIdentity G) hr
  | factor b split =>
    exact Classical.choice (split.left_power_labelled P.table (P.retainsIdentity G)
      (by norm_num) (mixedSupport_of_identity P.family (P.retainsIdentity G))
      (fullDeckRoot_nonzero P.family torsion f k) hr)

/-- Proper subtree access retains the exact saved slot and its port path. -/
def deckStoredPower (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (k : FullDeckIndex P.family torsion f)
    (j : FactorSaturation.ProperSlots (fullDeckRoot P.family torsion f k).2) :
    GeneralPowerExposure.PowerMacro P.table
      (FactorSaturation.slot (fullDeckRoot P.family torsion f k).2
        (FactorSaturation.properSlot (fullDeckRoot P.family torsion f k).2 j)).1.2 :=
  deckSlotPower G P torsion f core hcore k
    (FactorSaturation.properSlot (fullDeckRoot P.family torsion f k).2 j)

/-- Every actual transition focus or child in this fixed root tree has its
own constructed source macro, including the direct root and composites. -/
def deckSubtreePower (core : MinimumCore P.family) (hcore : core.signature = ⟨m+2,f⟩)
    (k : FullDeckIndex P.family torsion f) (u : TreeOccurrence (OI.K G))
    (hu : Holant.LocalDrafts.FinitePGL2.Stabilization.OccurrenceSchedule.StoredSubtree
      u (fullDeckRoot P.family torsion f k)) :
    GeneralPowerExposure.PowerMacro P.table u.1.2 := by
  let hs := savedSlot_cover hu
  have he := Classical.choose_spec hs
  rw [← he]
  exact deckSlotPower G P torsion f core hcore k (Classical.choose hs)

end Holant.LocalDrafts.RemoteWork.StableClosureV2
