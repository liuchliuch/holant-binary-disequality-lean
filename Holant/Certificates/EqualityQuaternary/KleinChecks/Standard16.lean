import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem standardCardsCorrect16 : ∀ ctx out a,
    cards .standard 16 ctx out a=cardFormula .standard 16 ctx out a := by decide +kernel

theorem standardTargetsCorrect16 : ∀ j,
    targets .standard 16 j=List.ofFn (targetFormula .standard 16 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
