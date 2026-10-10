import Holant.Proofs.Closure.ClosureCyclicCurrent

/-! Automatic exact-CURRENT-exit consumption of the constructed cyclic q4
boundary. The same stable constructor supplies q, torsion, minimum and rawDeck;
actual group guards are inspected internally. Higher cyclic/Reed--Muller local
obligations remain in the source frontier and are not called resolved here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (τ : ResidualTorsion P.family) (q : Signature (OI.K G) 4)
variable (core : MinimumCore P.family) (literal : core.signature = ⟨4,q⟩)
variable (currentDeck : ∀ g ∈ rawDeck P.family τ q, MatchingOrZero (actualTransfers P.family) g)

/-- Guard failures retain their actual current-group evidence. No completed
cyclic branch or source programme is supplied to the successful constructor. -/
inductive Attempt : Type 1
  | noncyclic (guard : ¬IsCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
  | small (cyclic : IsCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
      (guard : ¬3 ≤ Nat.card (D.group (ClosureSourceRows.embedding G) P.family τ))
  | produced (cyclic : IsCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
      (range : 3 ≤ Nat.card (D.group (ClosureSourceRows.embedding G) P.family τ))
      (completion : Completion G P τ q core literal currentDeck cyclic range)
      (sameFactory : completion = complete G P τ q core literal currentDeck cyclic range)

def attempt : Attempt G P τ q core literal currentDeck := by
  classical
  by_cases cyclic : IsCyclic (D.group (ClosureSourceRows.embedding G) P.family τ)
  · by_cases range : 3 ≤ Nat.card (D.group (ClosureSourceRows.embedding G) P.family τ)
    · exact .produced cyclic range (complete G P τ q core literal currentDeck cyclic range) rfl
    · exact .small cyclic range
  · exact .noncyclic cyclic

/-- Only the exact current stable q4 constructor enters this local boundary. -/
def ForExit (E : StructuralExit G P) : Type 1 := match E with
  | .stable 2 q _ _ τ minimum literal _ _ currentDeck =>
      Attempt G P τ q minimum literal currentDeck
  | _ => PUnit.{2}

/-- Source can consume its actual returned exit without a caller's success or
cyclic guard. No fresh q4 batch and no predecessor's deck is substituted. -/
def forStructuralExit (E : StructuralExit G P) : ForExit G P E := match E with
  | .unary _ _ _ => PUnit.unit
  | .infinite _ _ _ => PUnit.unit
  | .odd _ _ _ _ _ => PUnit.unit
  | .stable 0 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 1 _ _ _ _ _ _ _ _ _ => PUnit.unit
  | .stable 2 q _ _ τ minimum literal _ _ currentDeck =>
      attempt G P τ q minimum literal currentDeck
  | .stable (Nat.succ (Nat.succ (Nat.succ _))) _ _ _ _ _ _ _ _ _ => PUnit.unit

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
