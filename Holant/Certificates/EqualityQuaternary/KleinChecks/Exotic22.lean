import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect22 : ∀ ctx out a,
    cards .exotic 22 ctx out a=cardFormula .exotic 22 ctx out a :=
  cards_of_column_reindex .exotic 22 (by decide +kernel)

theorem exoticTargetsCorrect22 : ∀ j,
    targets .exotic 22 j=List.ofFn (targetFormula .exotic 22 j) :=
  targets_of_column_reindex .exotic 22 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
