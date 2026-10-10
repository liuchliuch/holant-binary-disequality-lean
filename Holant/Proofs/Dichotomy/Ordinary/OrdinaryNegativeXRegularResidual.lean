import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXSquares
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeFourthCompatibilitySource

/-! Actual obstruction reduction for the complete literal-X ordinary family.
The non-Product resource is internally chosen; all square and weight failures
have real original-G counting sources. The only returned mathematical residue
is one shared fourth-phase class and Affine squares on every original row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXRegularResidual
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionEq4FullSource (count arity table family)
export GlobalCloseCompletionEq4CSPSource (field)
end E
namespace N
export OrdinaryNegativeXNonproduct (blocks balanced row_closed row_nonproduct AllClosed)
end N
namespace S
export OrdinaryNegativeXSquares (AllSquaresAffine all_squares_or_countingHard)
end S
namespace F
export OrdinaryNegativeFourthCompatibilitySource (ambient Hard hard_or_compatible)
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
variable (P : Palette G) (o : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (E.field G P o) := (E.field G P o).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G P o)))

theorem closed_of_squares (h : S.AllSquaresAffine G P o) : N.AllClosed G P o := by
  intro j
  exact OrdinaryNegativeAffineSupportClosure.closed_of_square_affine _ (h j)

/-- Both tests cover every actual original label, not just a selected witness
or a finite list of descendants. The basis phase is chosen once for all rows. -/
def Ready : Prop := S.AllSquaresAffine G P o ∧ C.Compatible (F.ambient G P o)

include negative in
theorem hard_or_ready : F.Hard G ∨ Ready G P o := by
  rcases S.all_squares_or_countingHard G P o negative with squares|hard
  · have closed := closed_of_squares G P o squares
    rcases F.hard_or_compatible G P o (N.blocks G P o negative)
      (N.balanced G P o negative) (N.row_closed G P o negative closed)
      (N.row_nonproduct G P o negative) with hard|compatible
    · exact Or.inl hard
    · exact Or.inr ⟨squares,compatible⟩
  · exact Or.inl hard

include negative in
theorem ready_of_not_hard (h : ¬F.Hard G) : Ready G P o :=
  (hard_or_ready G P o negative).resolve_left h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXRegularResidual
end
