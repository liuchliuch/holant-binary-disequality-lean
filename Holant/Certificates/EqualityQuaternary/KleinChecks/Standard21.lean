import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect21 : ∀ ctx out a,
    cards .standard 21 ctx out a=cardFormula .standard 21 ctx out a :=
  cards_of_column_reindex .standard 21 (by decide +kernel)

theorem standardTargetsCorrect21 : ∀ j,
    targets .standard 21 j=List.ofFn (targetFormula .standard 21 j) :=
  targets_of_column_reindex .standard 21 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
