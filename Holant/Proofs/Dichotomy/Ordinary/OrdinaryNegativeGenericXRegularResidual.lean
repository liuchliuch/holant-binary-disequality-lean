import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXSquares
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXFourthCompatibilitySource

/-! Actual obstruction reduction for the complete literal-X ordinary family.
The non-Product resource is internally chosen; all square and weight failures
have real original-G counting sources. The only returned mathematical residue
is one shared fourth-phase class and Affine squares on every original row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXRegularResidual
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GenericLiteralXSource (count arity table family)
export GenericLiteralXSource (field)
end E
namespace N
export OrdinaryNegativeGenericXNonproduct (blocks balanced row_closed row_nonproduct AllClosed)
end N
namespace S
export OrdinaryNegativeGenericXSquares (AllSquaresAffine all_squares_or_countingHard)
end S
namespace F
export OrdinaryNegativeGenericXFourthCompatibilitySource (ambient Hard hard_or_compatible)
end F
namespace C
export OrdinaryNegativeFourthCompatibility (Compatible)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))

theorem closed_of_squares (h : S.AllSquaresAffine G src) : N.AllClosed G src := by
  intro j
  exact OrdinaryNegativeAffineSupportClosure.closed_of_square_affine _ (h j)

/-- Both tests cover every actual original label, not just a selected witness
or a finite list of descendants. The basis phase is chosen once for all rows. -/
def Ready : Prop := S.AllSquaresAffine G src ∧ C.Compatible (F.ambient G src)

include negative in
theorem hard_or_ready : F.Hard G ∨ Ready G src := by
  rcases S.all_squares_or_countingHard G src negative with squares|hard
  · have closed := closed_of_squares G src squares
    rcases F.hard_or_compatible G src (N.blocks G src negative)
      (N.balanced G src negative) (N.row_closed G src negative closed)
      (N.row_nonproduct G src negative) with hard|compatible
    · exact Or.inl hard
    · exact Or.inr ⟨squares,compatible⟩
  · exact Or.inl hard

include negative in
theorem ready_of_not_hard (h : ¬F.Hard G) : Ready G src :=
  (hard_or_ready G src negative).resolve_left h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXRegularResidual
end
