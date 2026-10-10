import Holant.Proofs.Dichotomy.Closure.Retained.GlobalCloseCompletionRetainedPredicateLeaf
import Holant.Proofs.Closure.ClosureFactorTreeAction
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! The retained nonaffine-prime selector in any one fixed algebraic basis,
including source K. The exact original-field factor tree and all its split
units/port orders survive; the basis is not claimed as a gadget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinAffineCoordinates
open Holant Holant.Tractable Holant.Algebraic
open Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace R
export GlobalCloseCompletionRetainedPredicateLeaf (SplitClosed Minimum retained_bad_prime exists_minimum)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem affine_split {f a b : AnySignature AlgebraicComplex} (split : ProperSplit f a b)
    (left : Affine a.2) (right : Affine b.2) : Affine f.2 := by
  have h := ((left.precompose (fun x i=>x (split.ports (.inl i)))
    (coordinates_isAffineMap (fun i=>split.ports (.inl i)))).mul
    (right.precompose (fun x i=>x (split.ports (.inr i)))
      (coordinates_isAffineMap (fun i=>split.ports (.inr i))))).scale (split.scale : AlgebraicComplex)
  rw [split.equation]
  exact h

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (B : InvertibleKernel)

def Predicate (f : AnySignature (OI.K G)) : Prop :=
  Affine (B.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f.2))

theorem split_closed : R.SplitClosed (Predicate G B) := by
  intro f a b split left right
  exact affine_split (ClosureFactorTreeAction.split B (split.map (ClosureSourceRows.embedding G))) left right

theorem retained_nonaffine_prime (i : Fin P.count)
    (bad : ¬Predicate G B ⟨P.arity i.val,P.table i⟩) :
    ∃g : AnySignature (OI.K G),g∈(P.trees i).leaves ∧ g∈P.family ∧ Prime g ∧
      g.1≤P.arity i.val ∧ ¬Predicate G B g :=
  R.retained_bad_prime G P (Predicate G B) (split_closed G B) i bad

theorem exists_minimum (bad : ∃i : Fin P.count,¬Predicate G B ⟨P.arity i.val,P.table i⟩) :
    Nonempty (R.Minimum G P (Predicate G B)) :=
  R.exists_minimum G P (Predicate G B) (split_closed G B) bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinAffineCoordinates
end
