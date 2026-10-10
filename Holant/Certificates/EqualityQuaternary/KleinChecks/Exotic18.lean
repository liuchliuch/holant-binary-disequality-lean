import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect18 : ∀ ctx out a,
    cards .exotic 18 ctx out a=cardFormula .exotic 18 ctx out a :=
  cards_of_column_reindex .exotic 18 (by decide +kernel)

theorem exoticTargetsCorrect18 : ∀ j,
    targets .exotic 18 j=List.ofFn (targetFormula .exotic 18 j) :=
  targets_of_column_reindex .exotic 18 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
