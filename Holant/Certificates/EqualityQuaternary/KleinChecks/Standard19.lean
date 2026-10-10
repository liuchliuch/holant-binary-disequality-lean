import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect19 : ∀ ctx out a,
    cards .standard 19 ctx out a=cardFormula .standard 19 ctx out a :=
  cards_of_column_reindex .standard 19 (by decide +kernel)

theorem standardTargetsCorrect19 : ∀ j,
    targets .standard 19 j=List.ofFn (targetFormula .standard 19 j) :=
  targets_of_column_reindex .standard 19 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
