import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Current
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification

/-! The native-M continuation has no higher-ancestor residual. Every genuinely
higher branch now installs whole-family ordinary two-pin/even-CSP access through
a real Eq4 graph. The remaining alternatives are the already implemented hard,
tractable, equality-anchor and singular-unary branches. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeMOrdinary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionMixedCurrent
open GlobalCloseCompletionNativeMContinuation (eoFamily CurrentTract)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A) (noPrior : A.source.done=∅)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion))

inductive Completion : Type 1 where
  | hard (negative : ¬EOTract (preprocess (eoFamily G base R noPrior N)))
  | tract (criterion : CurrentTract G base R)
  | anchor (receipt : StableDenseGaugeAnchorContinuation.AnchorReceipt G (palette G base R))
  | unary (singular : StableDenseGaugeCurrent.SingularReceipt G (palette G base R))
      (receipt : StableDenseGaugeUnary.UnaryReceipt G (palette G base R) singular)
  | ordinary (output : GlobalCloseCompletionEq4Graph.Output G (palette G base R))
      (obstruction : StableHigherCurrentOrdinaryTerminal.Obstruction
        (preprocess (GlobalCloseCompletionEq4FullSource.family G (palette G base R) output)))

def complete : Completion G base R noPrior N := by
  classical
  cases GlobalCloseCompletionNativeMContinuation.complete G base R noPrior N with
  | hard negative => exact .hard negative
  | tract criterion => exact .tract criterion
  | anchor receipt => exact .anchor receipt
  | unary singular receipt => exact .unary singular receipt
  | higher C basis noDense o higher =>
      let d := GlobalCloseCompletionEq4Current.output G base R noPrior N C basis noDense o higher
      by_cases tract : Tract (GlobalCloseCompletionEq4FullSource.family G (palette G base R) d)
      · exact .tract (GlobalCloseCompletionEq4Classification.tractX_of_tract G (palette G base R) d tract)
      · exact .ordinary d ((GlobalCloseCompletionEq4FullSource.rejected_iff G (palette G base R) d).mp tract)

/-- The Eq4 output is immediately consumed by the actual whole-family source,
so the new alternative does not hide a missing pin/equality compiler. -/
def Installed (c : Completion G base R noPrior N) : Type 1 :=
  match c with
  | .ordinary d _ => {p // p=GlobalCloseCompletionEq4FullSource.squareCSPSource G (palette G base R) d}
  | _ => PUnit.{2}

def install (c : Completion G base R noPrior N) : Installed G base R noPrior N c :=
  match c with
  | .ordinary d _ => ⟨GlobalCloseCompletionEq4FullSource.squareCSPSource G (palette G base R) d,rfl⟩
  | .hard _ => PUnit.unit
  | .tract _ => PUnit.unit
  | .anchor _ => PUnit.unit
  | .unary _ _ => PUnit.unit

structure Receipt : Type 1 where
  result : Completion G base R noPrior N
  resultIdentity : result=complete G base R noPrior N
  installed : Installed G base R noPrior N result

def produce : Receipt G base R noPrior N :=
  ⟨complete G base R noPrior N,rfl,install G base R noPrior N _⟩

def ForMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : Type 1 :=
  match M with
  | .monomial native => Receipt G base R noPrior native
  | _ => PUnit.{2}

def forMarking (M : ClosureMarkedSourceRouting.Marking (ClosureSourceRows.embedding G)
    (palette G base R).family R.final.ready.torsion) : ForMarking G base R noPrior M := by
  cases M with
  | monomial native => exact produce G base R noPrior native
  | smallTwo => exact PUnit.unit
  | smallFour => exact PUnit.unit
  | cyclic => exact PUnit.unit
  | bilinear => exact PUnit.unit
  | unshifted => exact PUnit.unit
  | shifted => exact PUnit.unit
  | platonic => exact PUnit.unit

def ForResult (result : GeneratedGroupWorklist.Result G base) : Type 1 :=
  match result with
  | .initialStop .. => PUnit.{2}
  | .prepared _ _ (.inl _) => PUnit.{2}
  | .prepared _ _ (.inr exhausted) =>
      ForMarking G base exhausted rfl (ClosureMarkedActualReceipts.produce G
        exhausted.final.source.palette exhausted.final.ready.torsion).physical.marking

def forResult (result : GeneratedGroupWorklist.Result G base) : ForResult G base result :=
  match result with
  | .initialStop .. => PUnit.unit
  | .prepared _ _ (.inl _) => PUnit.unit
  | .prepared _ _ (.inr exhausted) => forMarking G base exhausted rfl _

def original_current_nativeM_ordinary : ForResult G (Initial.palette G)
    (GeneratedGroupWorklist.result G (Initial.palette G)) :=
  forResult G (Initial.palette G) (GeneratedGroupWorklist.result G (Initial.palette G))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionNativeMOrdinary
end
