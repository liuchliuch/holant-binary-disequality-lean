import Holant.Certificates.PlatonicQuaternaryExits.DeficientData
import Holant.Certificates.OctahedralSeparator.RankCertificates

/-! The six literal A.24 outputs. All support and minor checks evaluate the
accepted reconstructed coefficient tensors in the faithful exact scalar field. -/
namespace Holant.Certificates.PlatonicDeficient
open Holant Holant.Certificates.OctahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- The leading three computational pair states, in lexicographic order. -/
def minorStates : Fin 3 → PairIndex := ![(false,false),(false,true),(true,false)]

/-- Exact support of the scalar tensor, rather than a claimed table size. -/
def scalarSupport (p : Fin 6) : Finset (Fin 4 → Bool) :=
  Finset.univ.filter (fun x => cachedBase (p.natAdd 9) x ≠ 0)

theorem scalar_support_ten : ∀ p : Fin 6, (scalarSupport p).card = 10 := by
  decide +kernel

theorem deficient_determinant_zero : ∀ p : Fin 6, ∀ r : Fin 3,
    (scalarFlatten r (cachedBase (p.natAdd 9))).det = 0 := by
  decide +kernel

theorem deficient_minor_nonzero : ∀ p : Fin 6, ∀ r : Fin 3,
    ((scalarFlatten r (cachedBase (p.natAdd 9))).submatrix minorStates minorStates).det ≠ 0 := by
  decide +kernel

/-- The source contracts original ports 1/3, retaining 2/4/5/6 in that order. -/
theorem contraction_ports :
    TetrahedralDeck.order 1 = ![0,2,1,3,4,5] ∧
      TetrahedralDeck.residual 1 = ![1,3,4,5] := by
  constructor <;> decide

end Holant.Certificates.PlatonicDeficient
