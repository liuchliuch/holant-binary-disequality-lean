import Holant.Proofs.Closure.ClosureCyclicCurrentGrowth
import Holant.Proofs.Closure.ClosureCyclicCurrentUnary

/-! In the actual old cyclic complete group, a directly realized outside card
must be singular. Its genuine saved unary leaf is therefore constructed without
assuming a prime binary or a successful singularity guard. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (τ : ResidualTorsion P.family)
variable (N : C.NativeCyclic (D.group (ClosureSourceRows.embedding G) P.family τ))
variable (o : OutsideReceipt G P N.m)

theorem outside_singular : Matrix.det (binaryMatrix (OutsideReceipt.output G P o)) = 0 := by
  by_contra nonsingular
  let B := binaryMatrix (OutsideReceipt.output G P o)
  have actual : ActualNonsingular P.family B := by
    refine ⟨?_,nonsingular⟩
    rw [binarySignature_binaryMatrix]
    exact ProjectiveOutput.source_actual G P o.card.signature o.access
  have det : Matrix.det (transfer B) ≠ 0 := by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero nonsingular det_X_ne_zero
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B) det
  have member : pglMk (OI.K G) U ∈ completeGroup P.family τ := by
    refine ⟨U,?_,rfl⟩
    refine ⟨B,actual,1,one_ne_zero,?_⟩
    ext u v
    exact (one_mul _).symm
  have phase := old_class_phase G P τ N B det member
  change CP.IsPhase N.m (CyclicBoundary.ActualCards.walshTransfer
    (RingHomRealization.mapSignature (ClosurePhysicalBridge.complexEmbedding G)
      (Holant.Projective.BoundedTorsion.binarySignature (binaryMatrix (OutsideReceipt.output G P o))))) at phase
  rw [binarySignature_binaryMatrix] at phase
  exact OutsideReceipt.source_outside G P o phase

def outsideUnary : UnaryReceipt G P o := unaryReceipt G P o (outside_singular G P τ N o)

def outsideExit : StructuralExit G (OutsideReceipt.palette G P o) :=
  UnaryReceipt.exit G P o (outsideUnary G P τ N o)
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
