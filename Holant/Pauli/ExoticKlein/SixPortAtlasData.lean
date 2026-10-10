import Holant.Pauli.ExoticKlein.SixPortAtlasModel

/-! Concrete seventeen-line candidates. Exhaustiveness, actual card identities
and projective distinctness are separate checked theorems. -/
namespace Holant.Pauli.ExoticKlein.SixPort.Atlas
noncomputable section

def candidateIndex : Fin 17 → Fin 960 :=
  ![0,192,244,300,344,384,436,492,536,608,660,716,760,800,852,908,952]

def candidateMultiplier : Fin 17 → ℕ :=
  ![1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1]

def candidateState : Fin 17 → DirectionTriple :=
  ![![none,none,none],![(some (directionEquiv 4)),(some (directionEquiv 12)),(some (directionEquiv 8))],![(some (directionEquiv 4)),(some (directionEquiv 12)),(some (directionEquiv 8))],![(some (directionEquiv 4)),(some (directionEquiv 12)),(some (directionEquiv 8))],![(some (directionEquiv 4)),(some (directionEquiv 12)),(some (directionEquiv 8))],![(some (directionEquiv 4)),(some (directionEquiv 8)),(some (directionEquiv 12))],![(some (directionEquiv 4)),(some (directionEquiv 8)),(some (directionEquiv 12))],![(some (directionEquiv 4)),(some (directionEquiv 8)),(some (directionEquiv 12))],![(some (directionEquiv 4)),(some (directionEquiv 8)),(some (directionEquiv 12))],![(some (directionEquiv 1)),(some (directionEquiv 3)),(some (directionEquiv 2))],![(some (directionEquiv 1)),(some (directionEquiv 3)),(some (directionEquiv 2))],![(some (directionEquiv 1)),(some (directionEquiv 3)),(some (directionEquiv 2))],![(some (directionEquiv 1)),(some (directionEquiv 3)),(some (directionEquiv 2))],![(some (directionEquiv 1)),(some (directionEquiv 2)),(some (directionEquiv 3))],![(some (directionEquiv 1)),(some (directionEquiv 2)),(some (directionEquiv 3))],![(some (directionEquiv 1)),(some (directionEquiv 2)),(some (directionEquiv 3))],![(some (directionEquiv 1)),(some (directionEquiv 2)),(some (directionEquiv 3))]]

def candidateScale2 : Fin 17 → Fin 4 → ℤ :=
  ![![2,0,0,0],![2,2,1,1],![2,2,-1,-1],![2,-2,1,-1],![2,-2,-1,1],![2,2,-1,-1],![2,2,1,1],![2,-2,-1,1],![2,-2,1,-1],![2,2,1,1],![2,2,-1,-1],![2,-2,1,-1],![2,-2,-1,1],![2,2,-1,-1],![2,2,1,1],![2,-2,-1,1],![2,-2,1,-1]]

def candidateInteger (i : Fin 17) (w : Fin 64) : GZ :=
  (candidateMultiplier i : GZ)*integerProduct (candidateIndex i) w

def candidate (i : Fin 17) : Signature ℂ 6 := normalizedProduct (candidateIndex i)

def candidateScale (i : Fin 17) (a : Fin 4) : ℂ := (candidateScale2 i a : ℂ)/2

end
end Holant.Pauli.ExoticKlein.SixPort.Atlas
