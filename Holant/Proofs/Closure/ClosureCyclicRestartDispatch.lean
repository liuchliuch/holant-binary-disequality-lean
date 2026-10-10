import Holant.Proofs.Closure.ClosureCyclicRestartGrowth

/-! Automatic re-entry and explicit terminal branches for the cyclic q4
subprotocol. Each growth branch prepares its installed palette internally and
uses only the literal fresh final exit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
attribute [local irreducible] ClosureCyclicCurrent.selected ClosureCyclicCurrent.run
  ClosureCyclicCurrent.installedPalette GeneratedGroupWorklist.result Growth.preparation Growth.exit

def IsQ4 {P : Palette G} : StructuralExit G P → Prop
  | .stable m _ _ _ _ _ _ _ _ _ => m = 2
  | _ => False

inductive Terminal (S : Node G) : Type 1
  | noncyclic (guard : ¬ IsCyclic (SourceGroup G S))
  | small (cyclic : IsCyclic (SourceGroup G S)) (guard : ¬ 3 ≤ Nat.card (SourceGroup G S))
  | endpoint (cyclic : IsCyclic (SourceGroup G S)) (range : 3 ≤ Nat.card (SourceGroup G S))
      (receipt : ClosureCyclicCurrent.EndpointReceipt G S.palette)
      (same : (ClosureCyclicCurrent.Result.endpoint receipt : ClosureCyclicCurrent.Result G S.palette
        (ClosureCyclicCurrent.selected G S.palette S.torsion cyclic range).m) =
        ClosureCyclicCurrent.run G S.palette S.torsion S.q S.core S.literal S.matching cyclic range)
  | unary (cyclic : IsCyclic (SourceGroup G S)) (range : 3 ≤ Nat.card (SourceGroup G S))
      (receipt : ClosureCyclicCurrent.OutsideReceipt G S.palette
        (ClosureCyclicCurrent.selected G S.palette S.torsion cyclic range).m)
      (domain : ClosureCyclicCurrent.OutsideDomain G S.palette receipt)
      (unary : ClosureCyclicCurrent.UnaryReceipt G S.palette receipt)
      (same : (ClosureCyclicCurrent.Result.outside receipt domain : ClosureCyclicCurrent.Result G S.palette
        (ClosureCyclicCurrent.selected G S.palette S.torsion cyclic range).m) =
        ClosureCyclicCurrent.run G S.palette S.torsion S.q S.core S.literal S.matching cyclic range)
  | installedStop (cyclic : IsCyclic (SourceGroup G S)) (range : 3 ≤ Nat.card (SourceGroup G S))
      (receipt : ClosureCyclicCurrent.DoubledReceipt G S.palette
        (ClosureCyclicCurrent.selected G S.palette S.torsion cyclic range).m)
      (same : (ClosureCyclicCurrent.Result.doubled receipt : ClosureCyclicCurrent.Result G S.palette
        (ClosureCyclicCurrent.selected G S.palette S.torsion cyclic range).m) =
        ClosureCyclicCurrent.run G S.palette S.torsion S.q S.core S.literal S.matching cyclic range)
      (stop : OccurrenceWorklist.Stop G (ClosureCyclicCurrent.installedPalette G S.palette receipt.doubled))
      (physical : RetainedFinalAccess.Access G (ClosureCyclicCurrent.installedPalette G S.palette receipt.doubled)
        (OccurrenceWorklist.Stop.structural G stop))
  | preparedOther (growth : Growth G S) (other : ¬ IsQ4 G growth.exit)

inductive Dispatch (S : Node G) : Type 1
  | terminal (result : Terminal G S)
  | next (T : Node G) (event : Step G S T)

/-- The same freshly returned q4 constructor supplies the next core and deck. -/
def dispatchGrowth (S : Node G) (g : Growth G S) : Dispatch G S := by
  cases hx : g.exit with
  | unary _ _ _ => exact .terminal (.preparedOther g (by rw [hx]; simp only [IsQ4,not_false_eq_true]))
  | infinite _ _ _ => exact .terminal (.preparedOther g (by rw [hx]; simp only [IsQ4,not_false_eq_true]))
  | odd _ _ _ _ _ => exact .terminal (.preparedOther g (by rw [hx]; simp only [IsQ4,not_false_eq_true]))
  | stable m q proper even torsion core literal noUnary noOdd matching =>
    obtain rfl := g.final_stable_residual_eq_two q proper core literal
    exact .next ⟨g.finalPalette,torsion,q,core,literal,noUnary,noOdd,matching⟩
      (.next g torsion q core literal noUnary noOdd matching hx)

def dispatchCompletion (S : Node G)
    (cyclic : IsCyclic (SourceGroup G S)) (range : 3 ≤ Nat.card (SourceGroup G S))
    (completion : ClosureCyclicCurrent.Completion G S.palette S.torsion S.q S.core S.literal S.matching cyclic range) :
    Dispatch G S := by
  rcases completion with ⟨branch,same,continuation⟩
  cases branch with
  | endpoint receipt => exact .terminal (.endpoint cyclic range receipt same)
  | outside receipt domain => exact .terminal (.unary cyclic range receipt domain continuation same)
  | doubled receipt =>
    change ClosureCyclicCurrent.DoubledContinuation G S.palette S.torsion
      (ClosureCyclicCurrent.selected G S.palette S.torsion cyclic range) receipt.doubled at continuation
    cases continuation with
    | stopped stop physical => exact .terminal (.installedStop cyclic range receipt same stop physical)
    | growth ready strict =>
      exact dispatchGrowth G S ⟨cyclic,range,receipt.doubled,same,ready,strict⟩

/-- Guard inspection and the complete physical source boundary are internal. -/
def dispatch (S : Node G) : Dispatch G S := by
  cases ClosureCyclicCurrent.attempt G S.palette S.torsion S.q S.core S.literal S.matching with
  | noncyclic guard => exact .terminal (.noncyclic guard)
  | small cyclic guard => exact .terminal (.small cyclic guard)
  | produced cyclic range completion sameFactory =>
    exact dispatchCompletion G S cyclic range completion

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
end
