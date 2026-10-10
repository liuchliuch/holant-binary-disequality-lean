import Holant.Proofs.Closure.ClosureCompatibleAlignmentCurrent

/-! Every proper normalized phase contraction, in every original order, is
derived from a literal CURRENT raw key with its source-field scalar.  This is
the first-contraction invariant for a protected two-tag contradiction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.TwoCardLocalization

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedral.NativeM
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable {r : ℕ} (f : Signature (OI.K G) (2*r+4))
variable (stable : ∀ g ∈ rawDeck P.family torsion f,
  Holant.Certificates.MatchingContractionClosure.MatchingOrZero (actualTransfers P.family) g)

include stable

theorem current_normalized_card_cases (order : Equiv.Perm (Fin (2*r+4)))
    (p : Bool) (t : {t : Scalar // Roots N.m t}) :
    normalizedCurrentCard G P torsion N f order p t = 0 ∨
      ClosureSixPort.AlgebraicRootMatching N.m (normalizedCurrentCard G P torsion N f order p t) := by
  classical
  by_cases zero : normalizedCurrentCard G P torsion N f order p t = 0
  · exact Or.inl zero
  · right
    let S := selectCurrentCard G P torsion N f order p t stable zero
    exact ⟨S.algebraic,S.algebraic_member,S.algebraic_scalar_nonzero,S.algebraic_equation⟩

/-- The actual combined original permutation covers an outside instruction;
no stability of a separately chosen/reindexed deck is supplied. -/
theorem current_outside_card_cases (original : Equiv.Perm (Fin (2*r+4)))
    (cut : Equiv.Perm (Fin (2*r+2))) (p : Bool) (t : {t : Scalar // Roots N.m t}) :
    outsideClose cut (M p t.val)
        (Tensor.reindex original.symm (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f)) = 0 ∨
      ClosureSixPort.AlgebraicRootMatching N.m
        (outsideClose cut (M p t.val)
          (Tensor.reindex original.symm (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f))) :=
  current_normalized_card_cases G P torsion N f stable ((outsideOrder cut).trans original) p t

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
