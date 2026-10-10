import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicPreparedResolution
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralZSign

/-! Concrete source consumption of the entire cyclic resolution. Every Eq4
alternative installs both ordinary pins and a literal Z label, retains all
old ordinary rows, and applies the genuine whole-family test. Positive tests
return the original current criterion; only the shared negative ordinary and
structural terminals remain, with their actual source data. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicResolvedSource
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace O
export GlobalCloseCompletionStopOrdinarySource (family family_exact native_family tract_iff_current)
end O
namespace E
export GlobalCloseCompletionC2PrimeCurrent (data old_included z_member)
end E
namespace R
export GlobalCloseCompletionCyclicQ4Resolution (Endpoint)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
abbrev CurrentTract := TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P))

theorem ordinary_mono (Q : Palette G) (old : P.family⊆Q.family) : O.family G P⊆O.family G Q := by
  rw [O.family_exact,O.native_family,O.family_exact,O.native_family]
  exact familyAction_mono sourceKBasis (Set.image_mono old)

theorem noncyclic_extension_strict (torsion : ResidualTorsion P.family)
    (cyclic : IsCyclic (completeGroup P.family torsion)) (Q : Palette G)
    (newTorsion : ResidualTorsion Q.family) (old : P.family⊆Q.family)
    (noncyclic : ¬IsCyclic (completeGroup Q.family newTorsion)) :
    completeGroup P.family torsion<completeGroup Q.family newTorsion := by
  apply lt_of_le_of_ne (completeGroup_mono old torsion newTorsion)
  intro same
  exact noncyclic (same ▸ cyclic)

theorem noncyclic_extension_decreases (torsion : ResidualTorsion P.family)
    (cyclic : IsCyclic (completeGroup P.family torsion)) (Q : Palette G)
    (newTorsion : ResidualTorsion Q.family) (old : P.family⊆Q.family)
    (noncyclic : ¬IsCyclic (completeGroup Q.family newTorsion)) :
    sourceGroupDefect Q.family newTorsion<sourceGroupDefect P.family torsion :=
  sourceGroupDefect_lt_of_strict torsion newTorsion
    (noncyclic_extension_strict G P torsion cyclic Q newTorsion old noncyclic)

structure Ordinary where
  source : GenericOrdinarySource.Data G
  old : O.family G P⊆GenericOrdinarySource.family G source
  zLabel : Fin source.size
  zLiteral : (⟨source.b zLabel.val,source.H zLabel⟩ : AnySignature source.K)=⟨2,NoXGeneralZSign.signature⟩
  negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G source))

inductive Completion : Type 1 where
  | tract (criterion : CurrentTract G P)
  | hard (proof : NoXWeightedAntiSquares.Hard G)
  | ordinary (data : Ordinary G P)
  | stopped (Q : Palette G) (old : P.family⊆Q.family) (stop : OccurrenceWorklist.Stop G Q)
  | other (base : Palette G) (A : GeneratedGroupWorklist.Active G base)
      (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
      (old : P.family⊆run.final.source.palette.family)
      (noncyclic : ¬IsCyclic (completeGroup run.final.source.palette.family run.final.ready.torsion))

theorem install (result : R.Endpoint G P) : Nonempty (Completion G P) := by
  classical
  cases result with
  | tract Q old criterion =>
    exact ⟨.tract ((O.tract_iff_current G P).mp (criterion.mono_family (ordinary_mono G P Q old)))⟩
  | hard proof => exact ⟨.hard proof⟩
  | stopped Q old stop => exact ⟨.stopped Q old stop⟩
  | other base A run noPrior old noncyclic => exact ⟨.other base A run noPrior old noncyclic⟩
  | anchor Q old anchor =>
    let source := E.data G Q anchor
    have kept : O.family G P⊆GenericOrdinarySource.family G source :=
      (ordinary_mono G P Q old).trans (E.old_included G Q anchor)
    by_cases tract : Tract (GenericOrdinarySource.family G source)
    · exact ⟨.tract ((O.tract_iff_current G P).mp (tract.mono_family kept))⟩
    · have z := E.z_member G Q anchor
      obtain ⟨j,literal⟩ := GlobalCloseCompletionUnaryIsotropicLift.z_exists source.K source.H z
      have exactZ : (⟨source.b j.val,source.H j⟩ : AnySignature source.K)=⟨2,NoXGeneralZSign.signature⟩ := by
        refine literal.trans ?_
        apply congrArg (fun f : Signature source.K 2=>(⟨2,f⟩ : AnySignature source.K))
        funext x
        cases h0 : x 0 <;> cases h1 : x 1 <;> rfl
      exact ⟨.ordinary ⟨source,kept,j,exactZ,(GenericOrdinarySource.rejected_iff G source).mp tract⟩⟩

/-- Restrict every terminal to an earlier literal source. In the ordinary
arm, the same graph dictionary, pins, Z label, and obstruction are retained. -/
def Completion.restrict {Q : Palette G} (old : P.family⊆Q.family)
    (result : Completion G Q) : Completion G P := by
  cases result with
  | tract criterion =>
    exact .tract ((O.tract_iff_current G P).mp
      (((O.tract_iff_current G Q).mpr criterion).mono_family (ordinary_mono G P Q old)))
  | hard proof => exact .hard proof
  | ordinary data =>
    exact .ordinary ⟨data.source,(ordinary_mono G P Q old).trans data.old,data.zLabel,data.zLiteral,data.negative⟩
  | stopped Q kept stop => exact .stopped Q (old.trans kept) stop
  | other base A run noPrior kept noncyclic =>
    exact .other base A run noPrior (old.trans kept) noncyclic

variable (base : Palette G) {A : GeneratedGroupWorklist.Active G base}
variable (run : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
variable (native : ClosureMarkedCyclic.NativeCyclic (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
  run.final.source.palette.family run.final.ready.torsion))

include noPrior native in
theorem exhausted : Nonempty (Completion G run.final.source.palette) := by
  obtain ⟨result⟩ := GlobalCloseCompletionCyclicPreparedResolution.exhausted G base run noPrior native
  exact install G run.final.source.palette result

def complete : Completion G run.final.source.palette := (exhausted G base run noPrior native).some

/-- The original preparation and all cyclic growth preserve the entire
base family, including labels not used by the selected minimum. -/
def fromBase : Completion G base :=
  Completion.restrict G base (GroupPreparedStability.source_retains G base run.final.source)
    (complete G base run noPrior native)

def ForMarking (marking : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    run.final.source.palette.family run.final.ready.torsion) : Type 1 := match marking with
  | .cyclic native=>Completion G base
  | _=>PUnit.{2}

include noPrior in
def forMarking (marking : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    run.final.source.palette.family run.final.ready.torsion) : ForMarking G base run marking := by
  cases marking with
  | cyclic native => exact fromBase G base run noPrior native
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | monomial => exact PUnit.unit
  | bilinear => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 := match result with
  | .initialStop ..=>PUnit.{2}
  | .prepared _ _ (.inl _)=>PUnit.{2}
  | .prepared _ _ (.inr run)=>ForMarking G base run
      (ClosureMarkedActualReceipts.produce G run.final.source.palette run.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result := by
  cases result with
  | initialStop => exact PUnit.unit
  | prepared ready trace result =>
    cases result with
    | inl => exact PUnit.unit
    | inr run => exact forMarking G base run rfl _

def original_current_cyclic_source : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicResolvedSource
end
