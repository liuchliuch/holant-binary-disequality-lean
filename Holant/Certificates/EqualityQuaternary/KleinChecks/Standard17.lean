import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect17 : ∀ ctx out a,
    cards .standard 17 ctx out a=cardFormula .standard 17 ctx out a :=
  cards_of_column_reindex .standard 17 (by decide +kernel)

theorem standardTargetsCorrect17 : ∀ j,
    targets .standard 17 j=List.ofFn (targetFormula .standard 17 j) :=
  targets_of_column_reindex .standard 17 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
