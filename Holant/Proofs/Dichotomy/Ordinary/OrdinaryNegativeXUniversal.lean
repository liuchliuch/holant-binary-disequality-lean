import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalBase
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalSuppliers
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeXUniversalMixing
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification

/-! The actual literal-X ordinary obstruction implies genuine counting
hardness of unchanged original G. Labels, charts, pinnings, minimum ranks,
phase classes, parity corrections, private recipes and finite mixing choices
are all selected and proved internally. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversal
open Computability Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionEq4FullSource (count arity table family)
export GlobalCloseCompletionEq4CSPSource (field)
end E
namespace Pn
export GlobalCloseCompletionEq4Classification
  (current CurrentTract affine_or_product_of_tract tractX_of_tract originalComputes)
end Pn
namespace F
export OrdinaryNegativeFourthCompatibilitySource (Hard)
end F
namespace W
export OrdinaryNegativeXMinimalWitnesses (hard_or_complementary_ready)
end W
namespace R
export OrdinaryNegativeXUniversalSuppliers (alpha_supply affine_supply)
end R
namespace M
export OrdinaryNegativeXUniversalMixing (evenBad_of_resources)
end M
namespace B
export OrdinaryNegativeXUniversalBase (hard_of_even)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (o : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (E.field G P o) := (E.field G P o).algebra'
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (E.family G P o)))

include negative in
/-- No hardness or classification backend appears among the hypotheses. -/
theorem countingHard : F.Hard G := by
  rcases W.hard_or_complementary_ready G P o negative with hard|ready
  · exact hard
  obtain ⟨squares,j,k,r,t,loA,hiA,loU,hiU,WA,WU,minA,minU,_common⟩ := ready
  rcases R.alpha_supply G P o j (squares j) WA loA hiA minA with even|⟨ka,⟨first⟩⟩
  · exact B.hard_of_even G P o negative even
  rcases R.affine_supply G P o k (squares k) WU loU hiU minU with even|⟨kb,⟨second⟩⟩
  · exact B.hard_of_even G P o negative even
  exact B.hard_of_even G P o negative (M.evenBad_of_resources (E.table G P o) ka kb first second)

/-- The actual full ordinary table has either its exact positive
classification or genuine counting hardness at the unchanged original G. -/
theorem tract_or_hard : Tract (E.family G P o) ∨ F.Hard G := by
  classical
  by_cases tract : Tract (E.family G P o)
  · exact Or.inl tract
  · exact Or.inr (countingHard G P o
      ((GlobalCloseCompletionEq4FullSource.rejected_iff G P o).mp tract))

include P o

/-- The positive alternative returns one common Affine or Product basis for
the entire retained current family, with its native X-edge compatibility. -/
theorem common_or_hard :
    (CommonKPresentationInKCoordinates affineClass (Pn.current G P) ∨
      CommonKPresentationInKCoordinates productClass (Pn.current G P)) ∨ F.Hard G := by
  rcases tract_or_hard G P o with tract|hard
  · exact Or.inl (Pn.affine_or_product_of_tract G P o tract)
  · exact Or.inr hard

/-- Fully discharged Eq4 terminal: both alternatives refer to the whole
original current family or the unchanged original counting problem. -/
theorem classified : Pn.CurrentTract G P ∨ F.Hard G := by
  rcases tract_or_hard G P o with tract|hard
  · exact Or.inl (Pn.tractX_of_tract G P o tract)
  · exact Or.inr hard

/-- The Eq4 terminal computes the unchanged original G in polynomial time
or proves genuine witness-counting hardness for those exact source bytes. -/
theorem inFP_or_countingHard :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) ∨ F.Hard G := by
  rcases classified G P o with tract|hard
  · exact Or.inl (StablePaletteTractability.original_inFP G P tract)
  · exact Or.inr hard


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeXUniversal
end
