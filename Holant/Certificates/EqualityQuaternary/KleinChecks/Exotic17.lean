import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect17 : ∀ ctx out a,
    cards .exotic 17 ctx out a=cardFormula .exotic 17 ctx out a :=
  cards_of_column_reindex .exotic 17 (by decide +kernel)

theorem exoticTargetsCorrect17 : ∀ j,
    targets .exotic 17 j=List.ofFn (targetFormula .exotic 17 j) :=
  targets_of_column_reindex .exotic 17 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
