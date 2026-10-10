import Holant.Certificates.EqualityQuaternary.KleinPlaneTensor

noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Finite
def standardParity : Fin 4 → Bool := ![true,false,true,false]
def standardMinus : Fin 4 → Bool := ![true,true,false,false]
def standardSign (j : Fin 4) : Scalar := if standardMinus j then -1 else 1
def standardSignQ (j : Fin 4) : Q := if standardMinus j then -1 else 1


end Holant.Certificates.EqualityQuaternary.Klein
