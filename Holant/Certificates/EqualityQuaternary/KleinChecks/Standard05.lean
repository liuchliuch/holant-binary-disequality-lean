import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect05 : ∀ ctx out a,
    cards .standard 5 ctx out a=cardFormula .standard 5 ctx out a :=
  cards_of_column_reindex .standard 5 (by decide +kernel)

theorem standardTargetsCorrect05 : ∀ j,
    targets .standard 5 j=List.ofFn (targetFormula .standard 5 j) :=
  targets_of_column_reindex .standard 5 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
