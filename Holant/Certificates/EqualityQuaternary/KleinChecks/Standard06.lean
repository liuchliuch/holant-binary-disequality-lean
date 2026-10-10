import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem standardCardsCorrect06 : ∀ ctx out a,
    cards .standard 6 ctx out a=cardFormula .standard 6 ctx out a :=
  cards_of_column_reindex .standard 6 (by decide +kernel)

theorem standardTargetsCorrect06 : ∀ j,
    targets .standard 6 j=List.ofFn (targetFormula .standard 6 j) :=
  targets_of_column_reindex .standard 6 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
