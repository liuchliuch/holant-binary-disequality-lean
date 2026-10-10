import Holant.Certificates.EqualityQuaternary.KleinCacheColumns

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem exoticCardsCorrect20 : ∀ ctx out a,
    cards .exotic 20 ctx out a=cardFormula .exotic 20 ctx out a :=
  cards_of_column_reindex .exotic 20 (by decide +kernel)

theorem exoticTargetsCorrect20 : ∀ j,
    targets .exotic 20 j=List.ofFn (targetFormula .exotic 20 j) :=
  targets_of_column_reindex .exotic 20 (by decide +kernel)

end Holant.Certificates.EqualityQuaternary.Klein.Finite
