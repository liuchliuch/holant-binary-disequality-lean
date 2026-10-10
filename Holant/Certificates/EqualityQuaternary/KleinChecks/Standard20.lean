import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect20 : ∀ ctx out a,
    cards .standard 20 ctx out a=cardFormula .standard 20 ctx out a :=
  cards_of_column_reindex .standard 20 (by decide +kernel)

theorem standardTargetsCorrect20 : ∀ j,
    targets .standard 20 j=List.ofFn (targetFormula .standard 20 j) :=
  targets_of_column_reindex .standard 20 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
