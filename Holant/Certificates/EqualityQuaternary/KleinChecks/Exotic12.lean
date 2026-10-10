import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect12 : ∀ ctx out a,
    cards .exotic 12 ctx out a=cardFormula .exotic 12 ctx out a :=
  cards_of_column_reindex .exotic 12 (by decide +kernel)

theorem exoticTargetsCorrect12 : ∀ j,
    targets .exotic 12 j=List.ofFn (targetFormula .exotic 12 j) :=
  targets_of_column_reindex .exotic 12 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
