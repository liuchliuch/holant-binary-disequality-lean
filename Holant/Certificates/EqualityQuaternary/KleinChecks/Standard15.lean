import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect15 : ∀ ctx out a,
    cards .standard 15 ctx out a=cardFormula .standard 15 ctx out a :=
  cards_of_column_reindex .standard 15 (by decide +kernel)

theorem standardTargetsCorrect15 : ∀ j,
    targets .standard 15 j=List.ofFn (targetFormula .standard 15 j) :=
  targets_of_column_reindex .standard 15 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
