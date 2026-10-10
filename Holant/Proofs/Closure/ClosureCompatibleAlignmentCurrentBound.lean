import Holant.Proofs.Closure.ClosureCompatibleAlignmentOneStep
import Holant.Proofs.Closure.ClosureCompatibleAlignmentAttempt

/-! Closed CURRENT-source common-matching factor-line bound.  No chosen
matching presentation, equality, two-tag programme or final minor is supplied.
The two samples keep their literal raw keys and original-field normalizations. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (order : Equiv.Perm (Fin (2*r+4)))
variable (sector : Bool → Bool) (phase : Bool → {t : Scalar // Roots N.m t})
variable (stable : ∀ g ∈ rawDeck P.family torsion f,
  Holant.Certificates.MatchingContractionClosure.MatchingOrZero (actualTransfers P.family) g)
variable (nonzero : ∀ b,normalizedCurrentCard G P torsion N f order (sector b) (phase b) ≠ 0)

def currentAlignedTables : Bool → Fin (r+1) → Mat :=
  let S := selectedCurrentPair G P torsion N f order sector phase stable nonzero
  alignedTables (fun b => (S b).ports) (fun b => (S b).factors)

theorem current_factor_line_bound (large : 2 ≤ r) (e j : Fin (r+1)) (different : e ≠ j) :
    ProjectivelyEqual (currentAlignedTables G P torsion N f order sector phase stable nonzero true e)
      (currentAlignedTables G P torsion N f order sector phase stable nonzero false e) ∨
    ProjectivelyEqual (currentAlignedTables G P torsion N f order sector phase stable nonzero true j)
      (currentAlignedTables G P torsion N f order sector phase stable nonzero false j) := by
  let S := selectedCurrentPair G P torsion N f order sector phase stable nonzero
  have same := current_selected_matchings_equal G P torsion N f order large stable
    (sector false) (sector true) (phase false) (phase true) (S false) (S true)
  let B := currentAlignedTables G P torsion N f order sector phase stable nonzero
  have member₀ : ∀ i,B false i ∈ groupM N.m := (S false).factors_member
  have member₁ : ∀ i,B true i ∈ groupM N.m :=
    alignedFactor_group (by have := N.range; omega) (S false).ports (S true).ports
      (S true).factors (S true).factors_member
  have equation₀ : Signature.contract (M (sector false) (phase false).val)
      (Tensor.reindex order.symm (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)) =
      MC.productValue (S false).ports (B false) (S false).algebraic.scalar :=
    (S false).coefficient_product
  have equation₁ : Signature.contract (M (sector true) (phase true).val)
      (Tensor.reindex order.symm (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)) =
      MC.productValue (S false).ports (B true) (S true).algebraic.scalar := by
    have source := (S true).coefficient_product
    rw [← alignedTables_product (fun b => (S b).ports) (fun b => (S b).factors)
      (fun b => (S b).algebraic.scalar) same true] at source
    exact source
  exact common_matching_one_step_bound N.range large _
    (fun cut γ t => current_outside_card_cases G P torsion N f stable order cut γ t)
    _ _ (S false).ports (B false) (B true) _ _ member₀ member₁
    (S false).algebraic_scalar_nonzero (S true).algebraic_scalar_nonzero equation₀ equation₁ e j different

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
