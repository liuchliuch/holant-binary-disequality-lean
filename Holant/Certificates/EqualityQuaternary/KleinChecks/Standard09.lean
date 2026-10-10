import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect09 : ∀ ctx out a,
    cards .standard 9 ctx out a=cardFormula .standard 9 ctx out a :=
  cards_of_column_reindex .standard 9 (by decide +kernel)

theorem standardTargetsCorrect09 : ∀ j,
    targets .standard 9 j=List.ofFn (targetFormula .standard 9 j) :=
  targets_of_column_reindex .standard 9 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
