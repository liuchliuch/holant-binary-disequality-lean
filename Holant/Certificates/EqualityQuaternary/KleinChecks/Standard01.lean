import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem standardCardsCorrect01 : ∀ ctx out a,
    cards .standard 1 ctx out a=cardFormula .standard 1 ctx out a := by decide +kernel

theorem standardTargetsCorrect01 : ∀ j,
    targets .standard 1 j=List.ofFn (targetFormula .standard 1 j) := by decide +kernel

end Holant.Certificates.EqualityQuaternary.Klein.Finite
