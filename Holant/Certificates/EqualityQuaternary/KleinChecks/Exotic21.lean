import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect21 : ∀ ctx out a,
    cards .exotic 21 ctx out a=cardFormula .exotic 21 ctx out a :=
  cards_of_column_reindex .exotic 21 (by decide +kernel)

theorem exoticTargetsCorrect21 : ∀ j,
    targets .exotic 21 j=List.ofFn (targetFormula .exotic 21 j) :=
  targets_of_column_reindex .exotic 21 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
