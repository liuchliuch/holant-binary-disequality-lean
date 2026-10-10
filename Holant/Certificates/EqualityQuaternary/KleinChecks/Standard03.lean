import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect03 : ∀ ctx out a,
    cards .standard 3 ctx out a=cardFormula .standard 3 ctx out a :=
  cards_of_column_reindex .standard 3 (by decide +kernel)

theorem standardTargetsCorrect03 : ∀ j,
    targets .standard 3 j=List.ofFn (targetFormula .standard 3 j) :=
  targets_of_column_reindex .standard 3 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
