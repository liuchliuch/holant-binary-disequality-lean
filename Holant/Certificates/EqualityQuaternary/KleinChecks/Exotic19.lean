import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect19 : ∀ ctx out a,
    cards .exotic 19 ctx out a=cardFormula .exotic 19 ctx out a :=
  cards_of_column_reindex .exotic 19 (by decide +kernel)

theorem exoticTargetsCorrect19 : ∀ j,
    targets .exotic 19 j=List.ofFn (targetFormula .exotic 19 j) :=
  targets_of_column_reindex .exotic 19 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
