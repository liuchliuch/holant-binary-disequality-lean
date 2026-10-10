import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinExoticPositive
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinExoticAntiRow
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedEqualFourth

/-! Actual stable exotic-Klein minimum quaternaries are classified in the
unchanged original-G problem. The positive result reconstructs one basis for
the whole current family; the negative result uses the real retained weighted
antidiagonal and the genuine no-X equal-fourth counting-hardness programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticResolved
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
namespace D
export GlobalCloseCompletionKleinExoticPins (data)
end D
namespace A
export GlobalCloseCompletionKleinExoticAntiRow (produce)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (exotic : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.exotic)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

include cardinal noncyclic exotic core literal stable in
theorem classified : GlobalCloseCompletionKleinEq4Source.CurrentTract G P ∨
    GlobalCloseCompletionKleinEq4Source.Hard G := by
  classical
  let src := D.data G P torsion cardinal noncyclic exotic q core literal stable
  by_cases tract : Tract (GenericOrdinarySource.family G src)
  · exact Or.inl (GlobalCloseCompletionKleinExoticPositive.tractX_of_tract
      G P torsion cardinal noncyclic exotic q core literal stable tract)
  · have negative := (GenericOrdinarySource.rejected_iff G src).mp tract
    let row := A.produce G P torsion cardinal noncyclic exotic q core literal stable
    exact Or.inr (NoXWeightedEqualFourth.countingHard G src row.label row.left row.right
      row.left_nonzero row.right_nonzero row.literal row.fourths negative)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticResolved
end
