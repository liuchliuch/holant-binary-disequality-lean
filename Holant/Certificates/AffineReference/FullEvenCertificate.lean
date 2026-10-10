import Holant.Certificates.AffineReference.FullEvenBlock0
import Holant.Certificates.AffineReference.FullEvenBlock1
import Holant.Certificates.AffineReference.FullEvenBlock2
import Holant.Certificates.AffineReference.FullEvenBlock3
import Holant.Certificates.AffineReference.FullEvenBlock4
import Holant.Certificates.AffineReference.FullEvenBlock5
import Holant.Certificates.AffineReference.FullEvenBlock6
import Holant.Certificates.AffineReference.FullEvenBlock7

namespace Holant.Certificates.AffineReference
open Holant.Certificates.TwelveLoops

def evenWitness (p : EvenParameters) : EvenWitness :=
  match p.2.1,p.2.2.1,p.2.2.2 with
  | false,false,false => witnessBlock0 (phaseIndex p.1)
  | false,false,true => witnessBlock1 (phaseIndex p.1)
  | false,true,false => witnessBlock2 (phaseIndex p.1)
  | false,true,true => witnessBlock3 (phaseIndex p.1)
  | true,false,false => witnessBlock4 (phaseIndex p.1)
  | true,false,true => witnessBlock5 (phaseIndex p.1)
  | true,true,false => witnessBlock6 (phaseIndex p.1)
  | true,true,true => witnessBlock7 (phaseIndex p.1)

theorem evenWitness_valid (p : EvenParameters) : ValidEvenWitness p (evenWitness p) := by
  obtain ⟨⟨a,b,c⟩,x,y,z⟩ := p
  cases x <;> cases y <;> cases z
  · exact witnessBlock0_valid a b c
  · exact witnessBlock1_valid a b c
  · exact witnessBlock2_valid a b c
  · exact witnessBlock3_valid a b c
  · exact witnessBlock4_valid a b c
  · exact witnessBlock5_valid a b c
  · exact witnessBlock6_valid a b c
  · exact witnessBlock7_valid a b c

end Holant.Certificates.AffineReference
