import Holant.Proofs.Closure.ClosureCyclicRestartReceipts

/-! Finite closed iteration of actual q4 cyclic growth. The original-field
finite-group defect proves termination; no future readiness is an input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

inductive Trace : Node G → Node G → Type 1
  | nil (S : Node G) : Trace S S
  | cons {S T U : Node G} (event : Step G S T) (rest : Trace T U) : Trace S U

def Trace.copy {S T : Node G} : Trace G S T → Copy G S.palette T.palette
  | .nil S => Copy.identity S.palette
  | .cons event rest => (event.copy G).comp (rest.copy)

def Trace.length {S T : Node G} : Trace G S T → ℕ
  | .nil _ => 0
  | .cons _ rest => rest.length + 1

theorem Trace.rank_bound {S T : Node G} (trace : Trace G S T) : trace.length G + T.rank G ≤ S.rank G := by
  induction trace with
  | nil _ => simp [length]
  | cons event rest ih =>
      have decrease := event.decreases G
      change _ < _ at decrease
      simp only [length]
      omega

structure Completion (S : Node G) : Type 1 where
  last : Node G
  trace : Trace G S last
  terminal : Terminal G last

def Completion.prepend {S T : Node G} (event : Step G S T) (rest : Completion G T) : Completion G S :=
  ⟨rest.last,.cons event rest.trace,rest.terminal⟩

def finish (S : Node G) : Completion G S :=
  (earlier_wellFounded G).fix (fun S recurse =>
    match dispatch G S with
    | .terminal terminal => ⟨S,.nil S,terminal⟩
    | .next T event => Completion.prepend G event (recurse T (event.decreases G))) S

abbrev Completion.palette {S : Node G} (result : Completion G S) : Palette G := result.terminal.palette G
def Completion.copy {S : Node G} (result : Completion G S) : Copy G S.palette (result.palette G) :=
  (result.trace.copy G).comp (result.terminal.copy G)

theorem Completion.finite_bound {S : Node G} (result : Completion G S) : result.trace.length G ≤ S.rank G :=
  le_trans (Nat.le_add_right _ _) (result.trace.rank_bound G)

/-- Entry consumes the exact current structural exit. Higher/other structural
branches are explicit unprocessed results of this q4 cyclic subprotocol. -/
inductive Result (P : Palette G) : StructuralExit G P → Type 1
  | other (exit : StructuralExit G P) (unprocessed : ¬ IsQ4 G exit) : Result P exit
  | cyclic (torsion : ResidualTorsion P.family) (q : Signature (OI.K G) 4)
      (core : MinimumCore P.family) (literal : core.signature = ⟨4,q⟩)
      (noUnary : ¬ RetainedUnary P.family) (noOdd : StabilizationMathematical.NoOdd P.family)
      (matching : ∀ f ∈ rawDeck P.family torsion q, MatchingOrZero (actualTransfers P.family) f)
      (completion : Completion G ⟨P,torsion,q,core,literal,noUnary,noOdd,matching⟩) :
      Result P (.stable 2 q (by decide) (by decide) torsion core literal noUnary noOdd matching)

def result (P : Palette G) (exit : StructuralExit G P) : Result G P exit := by
  cases exit with
  | unary u retained nonzero => exact .other _ (by simp [IsQ4])
  | infinite B actual infiniteOrder => exact .other _ (by simp [IsQ4])
  | odd f retained prime nonbinary odd => exact .other _ (by simp [IsQ4])
  | stable m q proper even torsion core literal noUnary noOdd matching =>
    cases m with
    | zero => exact .other _ (by simp [IsQ4])
    | succ m =>
      cases m with
      | zero => exact .other _ (by simp [IsQ4])
      | succ m =>
        cases m with
        | zero => exact .cyclic torsion q core literal noUnary noOdd matching (finish G ⟨P,torsion,q,core,literal,noUnary,noOdd,matching⟩)
        | succ m => exact .other _ (by simp [IsQ4])

def Result.palette {P : Palette G} {exit : StructuralExit G P} : Result G P exit → Palette G
  | .other _ _ => P
  | .cyclic _ _ _ _ _ _ _ completion => completion.palette G

def Result.copy {P : Palette G} {exit : StructuralExit G P} (R : Result G P exit) : Copy G P (R.palette G) := by
  cases R with
  | other _ _ => exact Copy.identity P
  | cyclic _ _ _ _ _ _ _ completion => exact completion.copy G

def Result.frontier {P : Palette G} {exit : StructuralExit G P} (R : Result G P exit) :=
  CurrentFrontier.build G (R.palette G)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
end
