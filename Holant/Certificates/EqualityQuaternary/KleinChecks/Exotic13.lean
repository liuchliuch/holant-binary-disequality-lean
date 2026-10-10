import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect13 : ∀ ctx out a,
    cards .exotic 13 ctx out a=cardFormula .exotic 13 ctx out a :=
  cards_of_column_reindex .exotic 13 (by decide +kernel)

theorem exoticTargetsCorrect13 : ∀ j,
    targets .exotic 13 j=List.ofFn (targetFormula .exotic 13 j) :=
  targets_of_column_reindex .exotic 13 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
