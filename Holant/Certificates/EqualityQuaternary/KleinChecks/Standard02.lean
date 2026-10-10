import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect02 : ∀ ctx out a,
    cards .standard 2 ctx out a=cardFormula .standard 2 ctx out a :=
  cards_of_column_reindex .standard 2 (by decide +kernel)

theorem standardTargetsCorrect02 : ∀ j,
    targets .standard 2 j=List.ofFn (targetFormula .standard 2 j) :=
  targets_of_column_reindex .standard 2 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
