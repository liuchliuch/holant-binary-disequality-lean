import Holant.Certificates.AffineEndpoint.WordCode
import Holant.BoundaryAction

namespace Holant.Certificates.AffineEndpoint
open Holant

 theorem coordinateAction_wordCodes {R : Type*} [CommSemiring R]
    (L : Fin 4 → Bool → Bool → R) (f : Signature R 4) (x : Fin 4 → Bool) :
    Signature.coordinateAction L f x=
      ∑y : Fin 16,(∏j : Fin 4,L j (x j) (codeWord y j))*f (codeWord y) := by
  exact (Equiv.sum_comp wordEquiv (fun y => (∏j : Fin 4,L j (x j) (y j))*f y)).symm

end Holant.Certificates.AffineEndpoint
