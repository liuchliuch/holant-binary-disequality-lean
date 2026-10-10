import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect14 : ∀ ctx out a,
    cards .exotic 14 ctx out a=cardFormula .exotic 14 ctx out a :=
  cards_of_column_reindex .exotic 14 (by decide +kernel)

theorem exoticTargetsCorrect14 : ∀ j,
    targets .exotic 14 j=List.ofFn (targetFormula .exotic 14 j) :=
  targets_of_column_reindex .exotic 14 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
