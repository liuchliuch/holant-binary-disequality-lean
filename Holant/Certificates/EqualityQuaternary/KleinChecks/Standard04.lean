import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect04 : ∀ ctx out a,
    cards .standard 4 ctx out a=cardFormula .standard 4 ctx out a :=
  cards_of_column_reindex .standard 4 (by decide +kernel)

theorem standardTargetsCorrect04 : ∀ j,
    targets .standard 4 j=List.ofFn (targetFormula .standard 4 j) :=
  targets_of_column_reindex .standard 4 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
