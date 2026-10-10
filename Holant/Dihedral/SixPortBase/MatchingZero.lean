import Holant.Certificates.NormalizedDihedralQ6.Data
import Holant.Dihedral.SectorRuling.PhysicalSectors

/-! A genuine matching coset forces a missing original-port parity sector.
The port permutation is extracted from the semantic matching-coset witness,
not from a finite atlas or an assumed sector classification. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.SectorRuling
open Holant.Dihedral.CompatibleCoefficientLine
open Holant.Certificates.NormalizedDihedralQ6
set_option backward.isDefEq.respectTransparency false

/-- The first matched original pair has a forbidden parity, with both analytic
endpoints identically zero in the explicit residual order. -/
theorem matching_coset_zero_sector (h : Signature Scalar 6) (S : Support)
    (hs : ∀ x, h x ≠ 0 ↔ x ∈ S) (hm : matchingCoset S) :
    ∃ order : Equiv.Perm (Fin 6), ∃ γ : Bool,
      sectorFirst (s:=2) (Tensor.reindex order.symm h) γ = 0 ∧
      sectorSecond (s:=2) (Tensor.reindex order.symm h) γ = 0 := by
  obtain ⟨π,c,hc⟩ := hm
  refine ⟨π,!(c 0),?_,?_⟩
  · funext x
    change h (fun i => pair false (!(c 0)) x (π.symm i)) = 0
    by_contra hn
    have hp := (hc _).mp ((hs _).mp hn) (0 : Fin 3)
    have hp' : (!(c 0)) = c 0 := by
      simpa [pair] using hp
    cases h0 : c 0 <;> simp_all
  · funext x
    change h (fun i => pair true (!(!(c 0))) x (π.symm i)) = 0
    by_contra hn
    have hp := (hc _).mp ((hs _).mp hn) (0 : Fin 3)
    have hp' : (!(c 0)) = c 0 := by
      simpa [pair] using hp
    cases h0 : c 0 <;> simp_all

end Holant.Dihedral.SixPortBase
