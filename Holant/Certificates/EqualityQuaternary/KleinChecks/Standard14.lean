import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect14 : ∀ ctx out a,
    cards .standard 14 ctx out a=cardFormula .standard 14 ctx out a :=
  cards_of_column_reindex .standard 14 (by decide +kernel)

theorem standardTargetsCorrect14 : ∀ j,
    targets .standard 14 j=List.ofFn (targetFormula .standard 14 j) :=
  targets_of_column_reindex .standard 14 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
