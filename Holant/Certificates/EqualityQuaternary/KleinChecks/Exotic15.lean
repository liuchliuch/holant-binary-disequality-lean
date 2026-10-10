import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect15 : ∀ ctx out a,
    cards .exotic 15 ctx out a=cardFormula .exotic 15 ctx out a :=
  cards_of_column_reindex .exotic 15 (by decide +kernel)

theorem exoticTargetsCorrect15 : ∀ j,
    targets .exotic 15 j=List.ofFn (targetFormula .exotic 15 j) :=
  targets_of_column_reindex .exotic 15 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
