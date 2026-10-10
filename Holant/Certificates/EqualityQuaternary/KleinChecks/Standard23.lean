import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem standardCardsCorrect23 : ∀ ctx out a,
    cards .standard 23 ctx out a=cardFormula .standard 23 ctx out a := by decide +kernel

theorem standardTargetsCorrect23 : ∀ j,
    targets .standard 23 j=List.ofFn (targetFormula .standard 23 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
