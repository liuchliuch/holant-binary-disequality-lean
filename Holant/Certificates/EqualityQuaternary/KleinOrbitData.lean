import Holant.Certificates.EqualityQuaternary.KleinPlaneTensor
import Holant.Certificates.EqualityQuaternary.KleinOrbitNetwork

/-! Explicit actual-group words taking each classified exotic plane to the
representative plane. Their full coefficient action is checked separately. -/
namespace Holant.Certificates.EqualityQuaternary.Klein.Orbit
open Finite

def paths : Fin 24 → List Op := ![[.swap 1,.swap 0,.dress 1 3,.dress 0 2],[.swap 1,.swap 0,.dress 1 2,.dress 0 2],[.swap 1,.swap 2,.dress 0 3],[.swap 1,.swap 2,.dress 0 2],[.dress 1 2],[.swap 2,.dress 0 2],[.swap 1,.swap 0,.dress 0 3],[.dress 0 3],[.swap 0,.dress 0 3],[.swap 0,.dress 0 2],[.dress 0 2],[.swap 1,.swap 0,.dress 0 2],[.swap 2,.dress 0 3],[.dress 1 3],[.dress 1 2,.dress 0 2],[.swap 0,.dress 1 2,.dress 0 2],[.swap 1,.swap 0,.dress 0 1],[.dress 0 1],[.swap 0,.dress 0 1],[.swap 0,.dress 1 3,.dress 0 2],[.dress 1 3,.dress 0 2],[.swap 1,.swap 0],[.swap 0],[]]

end Holant.Certificates.EqualityQuaternary.Klein.Orbit
