import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedPredicateLeaf
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinNonrealRestart

/-! A genuine finite-source restart for a smaller predicate counterexample.
The actual graph output is installed with its entire factor tree, the actual
GeneratedGroupWorklist result is consumed, and its retained bad-prime minimum
strictly decreases. No successor classifier or arbitrary-output closure is an
input. The whole old source and all its saved trees remain present. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionRetainedPredicateRestart
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace R
export GlobalCloseCompletionRetainedPredicateLeaf (SplitClosed Minimum exists_minimum)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
attribute [local irreducible] GeneratedGroupWorklist.result
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (q : AnySignature (OI.K G)) (nonzero : q.2≠0) (positive : 0<q.1)
variable (actual : Gadget.Realizes P.family .disequality q.2)

abbrev installed : Palette G := ProgrammeSaturation.palette G P q nonzero positive actual

def preparation : GeneratedGroupWorklist.Result G (installed G P q nonzero positive actual) :=
  GeneratedGroupWorklist.result G (installed G P q nonzero positive actual)
abbrev finalSource := (preparation G P q nonzero positive actual).finalSource G
  (installed G P q nonzero positive actual)
abbrev finalPalette : Palette G := (finalSource G P q nonzero positive actual).palette

def oldLabel (i : Fin P.count) : Fin (finalPalette G P q nonzero positive actual).count :=
  (finalSource G P q nonzero positive actual).rootLabel (RetainedFactorCatalogue.oldLabel G P q nonzero i)

theorem oldLabel_injective : Function.Injective (oldLabel G P q nonzero positive actual) :=
  (finalSource G P q nonzero positive actual).rootInjective.comp
    (RetainedFactorCatalogue.oldLabel_injective G P q nonzero)

theorem old_saved (i : Fin P.count) :
    Frontier.paletteRoot G (finalPalette G P q nonzero positive actual)
      (oldLabel G P q nonzero positive actual i)=Frontier.paletteRoot G P i :=
  ((finalSource G P q nonzero positive actual).rootSaved _).trans
    (ProgrammeSaturation.old_saved G P q nonzero positive actual i)

theorem retains_old : P.family⊆(finalPalette G P q nonzero positive actual).family := by
  rintro f ⟨i,rfl⟩
  exact ⟨oldLabel G P q nonzero positive actual i,
    congrArg Sigma.fst (old_saved G P q nonzero positive actual i)⟩

def rootLabel : Fin (finalPalette G P q nonzero positive actual).count :=
  (finalSource G P q nonzero positive actual).rootLabel (RetainedFactorCatalogue.rootLabel G P q nonzero)

theorem root_saved :
    Frontier.paletteRoot G (finalPalette G P q nonzero positive actual)
      (rootLabel G P q nonzero positive actual)=
      (⟨q,RetainedFactorCatalogue.tree G q nonzero⟩ : TreeOccurrence (OI.K G)) :=
  ((finalSource G P q nonzero positive actual).rootSaved _).trans
    (ProgrammeSaturation.root_saved G P q nonzero positive actual)

theorem output_retained : q∈(finalPalette G P q nonzero positive actual).family :=
  ⟨rootLabel G P q nonzero positive actual,congrArg Sigma.fst (root_saved G P q nonzero positive actual)⟩

variable (C : AnySignature (OI.K G)→Prop) (closed : R.SplitClosed C) (bad : ¬C q)

include closed bad in
theorem minimum_exists : Nonempty (R.Minimum G (finalPalette G P q nonzero positive actual) C) := by
  apply R.exists_minimum G (finalPalette G P q nonzero positive actual) C closed
  obtain ⟨i,hi⟩ := output_retained G P q nonzero positive actual
  refine ⟨i,?_⟩
  exact fun h=>bad (hi ▸ h)

include closed bad in
theorem minimum_strict (old : R.Minimum G P C)
    (new : R.Minimum G (finalPalette G P q nonzero positive actual) C)
    (smaller : q.1<old.signature.1) : new.signature.1<old.signature.1 :=
  old.strict_of_new_bad G P C (finalPalette G P q nonzero positive actual) new closed q
    (output_retained G P q nonzero positive actual) bad smaller

include closed bad in
theorem exists_strict_minimum (old : R.Minimum G P C) (smaller : q.1<old.signature.1) :
    ∃new : R.Minimum G (finalPalette G P q nonzero positive actual) C,
      new.signature.1<old.signature.1 := by
  obtain ⟨new⟩ := minimum_exists G P q nonzero positive actual C closed bad
  exact ⟨new,minimum_strict G P q nonzero positive actual C closed bad old new smaller⟩

variable (oldCore : MinimumCore P.family)

include oldCore in
theorem installed_nonbinary :
    ∃f∈(installed G P q nonzero positive actual).family,Prime f∧3≤f.1 :=
  ⟨oldCore.signature,ProgrammeSaturation.retains_old G P q nonzero positive actual oldCore.retained,
    oldCore.prime,oldCore.nonbinary⟩

def exit : StructuralExit G (finalPalette G P q nonzero positive actual) :=
  GroupPreparedStability.resultExit G (installed G P q nonzero positive actual)
    (preparation G P q nonzero positive actual)
    (installed_nonbinary G P q nonzero positive actual oldCore)

def exitAccess := RetainedFinalAccess.forStructuralExit G (finalPalette G P q nonzero positive actual)
  (exit G P q nonzero positive actual oldCore)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionRetainedPredicateRestart
end
