import Holant.Certificates.OctahedralSeparator.ExitData
import Holant.Certificates.OctahedralSeparator.CaseIndex

namespace Holant.Certificates.OctahedralSeparator

/-- The source's three printed projective directions for each mixed deficient
row, with the same normalization and original port convention. -/
def deficientDirections : Fin 2 → Fin 3 → Fin 4 → ℤ :=
  ![![![1,-1,0,-1],![1,-3,1,-1],![1,-3,-1,-1]],
    ![![0,2,1,1],![1,2,0,1],![1,2,1,0]]]

theorem deficient_directions_complete : ∀ f : Fin 2, ∀ p : Fin 6,
    ∃ k : Fin 3, outsideDirection (deficientRow f p)=deficientDirections f k := by decide

theorem deficient_directions_twice : ∀ f : Fin 2, ∀ k : Fin 3,
    (Finset.univ.filter (fun p : Fin 6 => outsideDirection (deficientRow f p)=deficientDirections f k)).card=2 := by decide

theorem deficient_directions_distinct : ∀ f : Fin 2, Function.Injective (deficientDirections f) := by decide

end Holant.Certificates.OctahedralSeparator
