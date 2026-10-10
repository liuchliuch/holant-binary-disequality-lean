import Holant.Proofs.Closure.GeneratedDeckTransport
import Holant.Proofs.Closure.GeneratedDeckTransportLabel
import Holant.Proofs.Closure.RetainedFinalAccess
import Holant.Proofs.Closure.OccurrenceBatch

/-! Charged scalar-corrected access to CURRENT raw cards without a minimum.
A nonzero current card can reuse the exact copied old-batch root label and
saved tree. The actual graph stays unchanged; its nonzero power correction is
handled by the existing fixed-field physical branch machine, not a free scalar
vertex. Zero raw keys and the stand-alone sentinel have actual graph access. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedDeckTransport
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness Holant.LocalDrafts.Hardness.GeneralExtraction

/-- Scalar transport restores the full power coefficient. -/
theorem blockPower_scale {L : Type*} [Field L] {n : ℕ} (f : Signature L n) (c : L) (r : ℕ) :
    Carrier.blockPower (c • f) r = c^r • Carrier.blockPower f r := by
  funext x
  simp [Carrier.blockPower, Finset.prod_mul_distrib]

/-- Same graph and source labels; only the explicit nonzero correction changes.
The existing physical branch machine charges this fixed original-field scalar. -/
def scalePower {L : Type*} [Field L] {s n : ℕ} {a : ℕ → ℕ}
    {T : (i : Fin s) → Signature L (a i.val)} {f : Signature L n}
    (M : GeneralPowerExposure.PowerMacro T f) (c : L) (hc : c ≠ 0) :
    GeneralPowerExposure.PowerMacro T (c • f) := by
  refine ⟨M.exponent, M.positive, M.scale * (c^M.exponent)⁻¹,
    mul_ne_zero M.scale_ne_zero (inv_ne_zero (pow_ne_zero _ hc)), M.network, M.labels, ?_⟩
  rw [M.value, blockPower_scale]
  funext x
  change M.scale * Carrier.blockPower f M.exponent x =
    (M.scale * (c^M.exponent)⁻¹) * (c^M.exponent * Carrier.blockPower f M.exponent x)
  rw [mul_assoc, ← mul_assoc ((c^M.exponent)⁻¹), inv_mul_cancel₀ (pow_ne_zero _ hc), one_mul]

def castPower {L : Type*} [Field L] {s n : ℕ} {a : ℕ → ℕ}
    {T : (i : Fin s) → Signature L (a i.val)} {f g : Signature L n}
    (literal : f = g) (M : GeneralPowerExposure.PowerMacro T f) :
    GeneralPowerExposure.PowerMacro T g := literal ▸ M

theorem castPower_network {L : Type*} [Field L] {s n : ℕ} {a : ℕ → ℕ}
    {T : (i : Fin s) → Signature L (a i.val)} {f g : Signature L n}
    (literal : f = g) (M : GeneralPowerExposure.PowerMacro T f) :
    HEq (castPower literal M).network M.network := by
  cases literal
  rfl

theorem castPower_labels {L : Type*} [Field L] {s n : ℕ} {a : ℕ → ℕ}
    {T : (i : Fin s) → Signature L (a i.val)} {f g : Signature L n}
    (literal : f = g) (M : GeneralPowerExposure.PowerMacro T f) (label : Fin s)
    (actual : ∀ v, M.labels.vertex v = label) :
    ∀ v, (castPower literal M).labels.vertex v = label := by
  cases literal
  exact actual

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P Q : Palette G) (retains : P.family ⊆ Q.family)
variable (oldTorsion : ResidualTorsion P.family) (currentTorsion : ResidualTorsion Q.family)
variable (sameGroup : completeGroup Q.family currentTorsion = completeGroup P.family oldTorsion)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family)

abbrev currentCard (k : RawCardKey m (completeGroup Q.family currentTorsion)) :=
  card P.family Q.family retains oldTorsion currentTorsion sameGroup f k

theorem oldNonzero (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0) :
    rawCard P.family oldTorsion f (currentCard G P Q retains oldTorsion currentTorsion sameGroup f k).oldKey ≠ 0 :=
  fun hz => nonzero ((currentCard G P Q retains oldTorsion currentTorsion sameGroup f k).zero_iff
    P.family Q.family retains oldTorsion currentTorsion sameGroup f |>.mpr hz)

def oldFullKey (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0) : FullDeckIndex P.family oldTorsion f :=
  .inr ⟨(currentCard G P Q retains oldTorsion currentTorsion sameGroup f k).oldKey,
    oldNonzero G P Q retains oldTorsion currentTorsion sameGroup f k nonzero⟩

/-- The old tree remains the literal once-saved old tree. No equality to a
newly chosen CURRENT factor tree is asserted. -/
structure RootReceipt (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0) where
  label : Fin Q.count
  saved : Frontier.paletteRoot G Q label = fullDeckRoot P.family oldTorsion f
    (oldFullKey G P Q retains oldTorsion currentTorsion sameGroup f k nonzero)

def copiedRootReceipt (hm : 2 ≤ m)
    (labels : Fin (OccurrenceBatch.palette G P oldTorsion f retained hm).count → Fin Q.count)
    (saved : ∀ i, Frontier.paletteRoot G Q (labels i) =
      Frontier.paletteRoot G (OccurrenceBatch.palette G P oldTorsion f retained hm) i)
    (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0) :
    RootReceipt G P Q retains oldTorsion currentTorsion sameGroup f k nonzero :=
  let old := oldFullKey G P Q retains oldTorsion currentTorsion sameGroup f k nonzero
  ⟨labels (RetainedCatalogue.deckLabel G P oldTorsion f old),
    (saved _).trans (RetainedCatalogue.deck_saved G P oldTorsion f old)⟩

def rootPower (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0)
    (r : RootReceipt G P Q retains oldTorsion currentTorsion sameGroup f k nonzero) :
    GeneralPowerExposure.PowerMacro Q.table
      (rawCard P.family oldTorsion f (currentCard G P Q retains oldTorsion currentTorsion sameGroup f k).oldKey) :=
  castAnyPower Q.table (congrArg Sigma.fst r.saved) (labelPower Q.table r.label)

theorem rootPower_exact_label (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0)
    (r : RootReceipt G P Q retains oldTorsion currentTorsion sameGroup f k nonzero) :
    ∀ v, (rootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).labels.vertex v = r.label :=
  castAnyPower_labels Q.table (congrArg Sigma.fst r.saved) (labelPower Q.table r.label)
    r.label (labelPower_exact_label Q.table r.label)

def currentRootPower (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0)
    (r : RootReceipt G P Q retains oldTorsion currentTorsion sameGroup f k nonzero) :
    GeneralPowerExposure.PowerMacro Q.table (rawCard Q.family currentTorsion f k) :=
  let c := currentCard G P Q retains oldTorsion currentTorsion sameGroup f k
  castPower c.equation.symm
    (scalePower (rootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r) c.scalar c.nonzero)

theorem currentRootPower_same_graph (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0)
    (r : RootReceipt G P Q retains oldTorsion currentTorsion sameGroup f k nonzero) :
    HEq (currentRootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).network
      (rootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).network :=
  castPower_network _ _

theorem currentRootPower_exact_label (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0)
    (r : RootReceipt G P Q retains oldTorsion currentTorsion sameGroup f k nonzero) :
    ∀ v, (currentRootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).labels.vertex v = r.label :=
  castPower_labels _ _ r.label (rootPower_exact_label G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r)

def rootToOriginal (k : RawCardKey m (completeGroup Q.family currentTorsion))
    (nonzero : rawCard Q.family currentTorsion f k ≠ 0)
    (r : RootReceipt G P Q retains oldTorsion currentTorsion sameGroup f k nonzero) :
    RetainedBranch.ToOriginalProgramme G Q ⟨m,rawCard Q.family currentTorsion f k⟩ :=
  RetainedBranch.toOriginal G Q _ (currentRootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r)

def rootFromOriginal (k : RawCardKey m (completeGroup Q.family currentTorsion)) :
    RetainedBranch.FromOriginalProgramme G Q ⟨m,rawCard Q.family currentTorsion f k⟩ :=
  RetainedBranch.fromOriginal G Q _

/-- Actual old-key graph over Q, including an old key evaluating to zero.
It is available from retained f without a minimum-core premise. -/
def oldRawDirect (k : RawCardKey m (completeGroup P.family oldTorsion)) :
    DeckDirect Q.family (rawCard P.family oldTorsion f k) :=
  DeckDirect.ofRealizes (Q.retainsIdentity G)
    ((rawCard_realizes_exact P.family oldTorsion (P.retainsIdentity G) (by norm_num) f
      (Gadget.realizes_of_mem P.family .disequality f retained) k).mono retains)

/-- The zero sentinel uses a real arity-m graph and the charged literal-I/X
closed zero component; set membership alone is not a diagram receipt. -/
def zeroDirect : DeckDirect Q.family (0 : Signature (OI.K G) m) :=
  DeckDirect.zeroFrom (Q.retainsIdentity G)
    (oldRawDirect G P Q retains oldTorsion f retained
      (fun _ => none,Equiv.refl _,1,false)).realizes

def zeroToOriginal : RetainedBranch.ToOriginalProgramme G Q ⟨m, (0 : Signature (OI.K G) m)⟩ :=
  RetainedBranch.toOriginal G Q _
    (DeckDirect.directPower Q.table (Q.retainsIdentity G)
      (zeroDirect G P Q retains oldTorsion f retained).realizes)

def zeroFromOriginal : RetainedBranch.FromOriginalProgramme G Q ⟨m, (0 : Signature (OI.K G) m)⟩ :=
  RetainedBranch.fromOriginal G Q _

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedDeckTransport
end
