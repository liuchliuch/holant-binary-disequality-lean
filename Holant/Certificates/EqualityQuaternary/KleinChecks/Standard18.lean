import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect18 : ∀ ctx out a,
    cards .standard 18 ctx out a=cardFormula .standard 18 ctx out a :=
  cards_of_column_reindex .standard 18 (by decide +kernel)

theorem standardTargetsCorrect18 : ∀ j,
    targets .standard 18 j=List.ofFn (targetFormula .standard 18 j) :=
  targets_of_column_reindex .standard 18 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
