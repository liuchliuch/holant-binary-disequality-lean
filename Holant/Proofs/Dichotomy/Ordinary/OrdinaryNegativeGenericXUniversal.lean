import Holant.Proofs.Dichotomy.General.GenericLiteralXSource
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversalBase
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeGenericXUniversalSuppliers
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalMixing

/-! The actual literal-X ordinary obstruction implies genuine counting
hardness of unchanged original G. Labels, charts, pinnings, minimum ranks,
phase classes, parity corrections, private recipes and finite mixing choices
are all selected and proved internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXUniversal
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GenericLiteralXSource (count arity table family)
export GenericLiteralXSource (field)
end E
namespace F
export OrdinaryNegativeGenericXFourthCompatibilitySource (Hard)
end F
namespace W
export OrdinaryNegativeGenericXMinimalWitnesses (hard_or_complementary_ready)
end W
namespace R
export OrdinaryNegativeGenericXUniversalSuppliers (alpha_supply affine_supply)
end R
namespace M
export OrdinaryNegativeXUniversalMixing (evenBad_of_resources)
end M
namespace B
export OrdinaryNegativeGenericXUniversalBase (hard_of_even)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericLiteralXSource.Data G)
local instance : Algebra ℚ (E.field G src) := (E.field G src).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G src)))

include negative in
/-- No hardness or classification backend appears among the hypotheses. -/
theorem countingHard : F.Hard G := by
  rcases W.hard_or_complementary_ready G src negative with hard|ready
  · exact hard
  obtain ⟨squares,j,k,r,t,loA,hiA,loU,hiU,WA,WU,minA,minU,_common⟩ := ready
  rcases R.alpha_supply G src j (squares j) WA loA hiA minA with even|⟨ka,⟨first⟩⟩
  · exact B.hard_of_even G src negative even
  rcases R.affine_supply G src k (squares k) WU loU hiU minU with even|⟨kb,⟨second⟩⟩
  · exact B.hard_of_even G src negative even
  exact B.hard_of_even G src negative (M.evenBad_of_resources (E.table G src) ka kb first second)

/-- The actual full ordinary table has either its exact positive
classification or genuine counting hardness at the unchanged original G. -/
theorem tract_or_hard : Tract (E.family G src) ∨ F.Hard G := by
  classical
  by_cases tract : Tract (E.family G src)
  · exact Or.inl tract
  · exact Or.inr (countingHard G src
      ((GenericLiteralXSource.rejected_iff G src).mp tract))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeGenericXUniversal
end
