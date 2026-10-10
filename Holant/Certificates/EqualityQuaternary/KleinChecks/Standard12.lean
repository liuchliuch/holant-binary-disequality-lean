import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect12 : ∀ ctx out a,
    cards .standard 12 ctx out a=cardFormula .standard 12 ctx out a :=
  cards_of_column_reindex .standard 12 (by decide +kernel)

theorem standardTargetsCorrect12 : ∀ j,
    targets .standard 12 j=List.ofFn (targetFormula .standard 12 j) :=
  targets_of_column_reindex .standard 12 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
