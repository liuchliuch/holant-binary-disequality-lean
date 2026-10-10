import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect08 : ∀ ctx out a,
    cards .standard 8 ctx out a=cardFormula .standard 8 ctx out a :=
  cards_of_column_reindex .standard 8 (by decide +kernel)

theorem standardTargetsCorrect08 : ∀ j,
    targets .standard 8 j=List.ofFn (targetFormula .standard 8 j) :=
  targets_of_column_reindex .standard 8 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
