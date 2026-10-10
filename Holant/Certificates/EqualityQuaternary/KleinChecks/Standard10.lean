import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect10 : ∀ ctx out a,
    cards .standard 10 ctx out a=cardFormula .standard 10 ctx out a :=
  cards_of_column_reindex .standard 10 (by decide +kernel)

theorem standardTargetsCorrect10 : ∀ j,
    targets .standard 10 j=List.ofFn (targetFormula .standard 10 j) :=
  targets_of_column_reindex .standard 10 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
