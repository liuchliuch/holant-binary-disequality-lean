import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect11 : ∀ ctx out a,
    cards .standard 11 ctx out a=cardFormula .standard 11 ctx out a :=
  cards_of_column_reindex .standard 11 (by decide +kernel)

theorem standardTargetsCorrect11 : ∀ j,
    targets .standard 11 j=List.ofFn (targetFormula .standard 11 j) :=
  targets_of_column_reindex .standard 11 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
