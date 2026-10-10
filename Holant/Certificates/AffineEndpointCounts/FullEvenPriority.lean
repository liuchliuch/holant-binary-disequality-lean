import Holant.Certificates.AffineEndpointCounts.FullEvenBlock0
import Holant.Certificates.AffineEndpointCounts.FullEvenBlock1
import Holant.Certificates.AffineEndpointCounts.FullEvenBlock2
import Holant.Certificates.AffineEndpointCounts.FullEvenBlock3
import Holant.Certificates.AffineEndpointCounts.FullEvenBlock4
import Holant.Certificates.AffineEndpointCounts.FullEvenBlock5
import Holant.Certificates.AffineEndpointCounts.FullEvenBlock6
import Holant.Certificates.AffineEndpointCounts.FullEvenBlock7

namespace Holant.Certificates.AffineEndpointCounts
open Holant.Certificates.AffineReference

theorem evenWitness_first (p : EvenParameters) : FirstEvenWitness p (evenWitness p) := by
  obtain ⟨⟨a,b,c⟩,x,y,z⟩ := p
  cases x <;> cases y <;> cases z
  · exact fullEvenBlock0_first a b c
  · exact fullEvenBlock1_first a b c
  · exact fullEvenBlock2_first a b c
  · exact fullEvenBlock3_first a b c
  · exact fullEvenBlock4_first a b c
  · exact fullEvenBlock5_first a b c
  · exact fullEvenBlock6_first a b c
  · exact fullEvenBlock7_first a b c

end Holant.Certificates.AffineEndpointCounts
