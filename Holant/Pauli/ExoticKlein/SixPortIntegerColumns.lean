import Holant.Pauli.ExoticKlein.SixPortIntegerModel
import Holant.Pauli.ExoticKlein.SixPortFiniteTable

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators

def actualIntegerColumn (context : Fin 60) (g : Fin 4) (d : Fin 48) (word : Fin 16) : GZ :=
  ∑ u : Bool, ∑ v : Bool, integerDual4 (labelEquiv (contextEquiv context).2) u v*
    (let x := fillOrdered (contextEquiv context).1 u v ((wordEquiv 4).symm word)
     EOver integerI (labelEquiv g) (x 0) (x 1)*directionTensorOver integerI (directionEquiv d) (tail4 x))

def optionalIntegerColumn (columns : Fin 60 → Fin 4 → Fin 48 → Fin 16 → GZ)
    (state : DirectionTriple) (context : Fin 60) (word : Fin 16) (g : Fin 4) : GZ :=
  match cardDirections state g with
  | none => 0
  | some d => columns context g (directionEquiv.symm d) word

theorem integerCardMatrix_as_columns (state : DirectionTriple) :
    integerCardMatrix state = optionalIntegerColumn actualIntegerColumn state := by
  funext context word g
  cases hd : cardDirections state g with
  | none => simp [integerCardMatrix,optionalIntegerColumn,hd,optionDirectionOver]
  | some d => simp [integerCardMatrix,optionalIntegerColumn,actualIntegerColumn,hd,optionDirectionOver]

end
end Holant.Pauli.ExoticKlein.SixPort
