import Holant.Signature

/-! Actual coefficient addresses of one finite ordered original dictionary. -/
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralCommonField
abbrev OriginalIndex (s : ℕ) (arity : ℕ → ℕ) := Σ i : Fin s, (Fin (arity i.val) → Bool)
end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralCommonField
