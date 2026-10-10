import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect13 : ∀ ctx out a,
    cards .standard 13 ctx out a=cardFormula .standard 13 ctx out a :=
  cards_of_column_reindex .standard 13 (by decide +kernel)

theorem standardTargetsCorrect13 : ∀ j,
    targets .standard 13 j=List.ofFn (targetFormula .standard 13 j) :=
  targets_of_column_reindex .standard 13 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
