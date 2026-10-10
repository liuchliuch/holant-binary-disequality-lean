import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect22 : ∀ ctx out a,
    cards .standard 22 ctx out a=cardFormula .standard 22 ctx out a :=
  cards_of_column_reindex .standard 22 (by decide +kernel)

theorem standardTargetsCorrect22 : ∀ j,
    targets .standard 22 j=List.ofFn (targetFormula .standard 22 j) :=
  targets_of_column_reindex .standard 22 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
