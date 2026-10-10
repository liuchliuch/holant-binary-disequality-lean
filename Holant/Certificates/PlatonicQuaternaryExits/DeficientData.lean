import Holant.Certificates.OctahedralSeparator.BaseCache
import Holant.Certificates.OctahedralSeparator.TensorSemantics
import Holant.Certificates.OctahedralSeparator.GroupRepresentatives
import Holant.Certificates.IcosahedralSeparator.UniformOutputCode

/-! Literal six deficient qπ and their uniform contractions. Exact finite checks
use the faithful coefficient algebras, with no external computation trusted. -/
namespace Holant.Certificates.PlatonicQuaternaryExits.Deficient
open Holant Holant.Certificates.OctahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- Source reconstructed 1/3 contraction, surviving original ports2/4/5/6. -/
noncomputable def output (p : Fin 6) : Signature ℂ 4 := complexTensor (deficientCard p)

def order24 : Equiv.Perm (Fin 4) where
  toFun := ![2,0,3,1]
  invFun := ![1,3,0,2]
  left_inv := by decide
  right_inv := by decide

def standardBinary : Fin 6 → Mat :=
  ![mat (coeff (1/4) 0 (-1/4) 0) 0 0 (coeff (1/4) 0 (1/4) 0),
    mat (rat (1/4)) (rat (1/4)) (rat (-1/4)) (rat (1/4)),
    mat (rat (1/4)) (coeff 0 0 (-1/4) 0) (coeff 0 0 (-1/4) 0) (rat (1/4)),
    mat (rat (1/4)) (rat (1/4)) (rat (-1/4)) (rat (1/4)),
    mat (coeff (1/4) 0 (-1/4) 0) 0 0 (coeff (1/4) 0 (1/4) 0),
    mat (rat (1/4)) (coeff 0 0 (-1/4) 0) (coeff 0 0 (-1/4) 0) (rat (1/4))]

def octahedralBinary : Fin 6 → Mat :=
  ![mat (coeff (-1/4) 0 (-1/2) 0) (coeff (-1/4) 0 0 0) (coeff (1/4) 0 0 0) (coeff (-1/4) 0 (1/2) 0),
    mat (coeff (-1/4) 0 0 0) (coeff (-1/2) 0 (-1/4) 0) (coeff (1/2) 0 (-1/4) 0) (coeff (-1/4) 0 0 0),
    mat (coeff (-1/4) 0 (-1/4) 0) (coeff 0 0 (-1/2) 0) (coeff 0 0 (-1/2) 0) (coeff (-1/4) 0 (1/4) 0),
    mat (coeff (-1/4) 0 (-1/4) 0) (coeff (-1/2) 0 0 0) (coeff (1/2) 0 0 0) (coeff (-1/4) 0 (1/4) 0),
    mat (coeff (-1/4) 0 (-1/2) 0) (coeff 0 0 (-1/4) 0) (coeff 0 0 (-1/4) 0) (coeff (-1/4) 0 (1/2) 0),
    mat (coeff (-1/4) 0 0 0) (coeff (-1/4) 0 (-1/2) 0) (coeff (1/4) 0 (-1/2) 0) (coeff (-1/4) 0 0 0)]

/-- The source's second displayed deficient tensor uses uniform S⊗4. This is
only a definition of the original q' coefficients, never a physical gadget. -/
def primeTensor (p : Fin 6) : Signature Scalar 4 :=
  Signature.coordinateAction (fun _ => inverseConjugator 1) (cachedBase (Fin.natAdd 9 p))
noncomputable def primeOutput (p : Fin 6) : Signature ℂ 4 := complexTensor (primeTensor p)
def primeKernel : Mat := theta 1 (standard 11)
def primeBinary : Fin 6 → Mat :=
  ![mat (coeff 0 (1/64) 0 0) (coeff 0 (3/64) (-1/32) 0) (coeff 0 (3/64) (1/32) 0) (coeff 0 (-1/64) 0 0),
    mat (coeff 0 (1/32) (-1/32) 0) (coeff 0 (1/32) (-1/32) 0) (coeff 0 (1/32) (1/32) 0) (coeff 0 (-1/32) (-1/32) 0),
    mat (coeff 0 (1/64) (-1/32) 0) (coeff 0 (3/64) 0 0) (coeff 0 (3/64) 0 0) (coeff 0 (-1/64) (-1/32) 0),
    mat (coeff 0 (1/32) (-1/32) 0) (coeff 0 (1/32) (-1/32) 0) (coeff 0 (1/32) (1/32) 0) (coeff 0 (-1/32) (-1/32) 0),
    mat (coeff 0 (1/64) 0 0) (coeff 0 (3/64) (-1/32) 0) (coeff 0 (3/64) (1/32) 0) (coeff 0 (-1/64) 0 0),
    mat (coeff 0 (1/64) (-1/32) 0) (coeff 0 (3/64) 0 0) (coeff 0 (3/64) 0 0) (coeff 0 (-1/64) (-1/32) 0)]

theorem cached_deficient (p : Fin 6) : cachedBase (Fin.natAdd 9 p)=deficientCard p := by
  simpa only [baseCard,Fin.addCases_right] using base_exact (Fin.natAdd 9 p)

theorem standard_binary_check : ∀ p : Fin 6, ∀ a b : Bool,
    standardBinary p a b=Signature.contract (q 0) (cachedBase (Fin.natAdd 9 p)) ![a,b] := by
  decide +kernel

theorem octahedral_binary_check : ∀ p : Fin 6, ∀ a b : Bool,
    octahedralBinary p a b=Signature.contract (q 0)
      (Tensor.reindex order24 (cachedBase (Fin.natAdd 9 p))) ![a,b] := by decide +kernel

theorem prime_binary_check : ∀ p : Fin 6, ∀ a b : Bool,
    primeBinary p a b=Signature.contract primeKernel (primeTensor p) ![a,b] := by
  intro p
  fin_cases p <;> decide +kernel

theorem standard_determinant : ∀ p : Fin 6, determinant (standardBinary p)=rat (1/8) := by decide +kernel

theorem octahedral_determinant : ∀ p : Fin 6, determinant (octahedralBinary p)=rat (3/8) := by decide +kernel

theorem octahedral_different : ∀ p : Fin 6, ∀ k : Fin 24, ∃ a b c d : Bool,
    mm (octahedralBinary p) flip a b*standard k c d ≠
      mm (octahedralBinary p) flip c d*standard k a b := by
  intro p
  fin_cases p <;> decide +kernel

theorem prime_determinant : ∀ p : Fin 6, determinant (primeBinary p)=rat (-3/512) := by
  intro p
  fin_cases p <;> decide +kernel

theorem prime_different : ∀ p : Fin 6, ∀ k : Fin 24, ∃ a b c d : Bool,
    pull 1 (mm (primeBinary p) flip) a b*standard k c d ≠
      pull 1 (mm (primeBinary p) flip) c d*standard k a b := by
  intro p
  fin_cases p <;> decide +kernel

namespace Golden
open Holant.Certificates.IcosahedralSeparator
open Holant.Certificates.RainbowOrbit

def index : Fin 6 → Fin 3 := ![0,1,2,1,0,2]
def realPart : Fin 3 → Bool → Bool → ℤ :=
  ![(fun a b => if a=b then 1 else 0),
    (fun a b => if a && !b then -1 else 1),
    (fun a b => if a=b then 1 else 0)]
def imagPart : Fin 3 → Bool → Bool → ℤ :=
  ![(fun a b => if a=b then if a then 1 else -1 else 0),
    (fun _ _ => 0),(fun a b => if a=b then 0 else -1)]
def binaryCode (i : Fin 3) (a b : Bool) : GScalar :=
  (GoldenInt.ofInt (realPart i a b),GoldenInt.ofInt (imagPart i a b))
def transferCode (i : Fin 3) (a b : Bool) : GScalar := binaryCode i a (!b)

theorem different : ∀ i : Fin 3, ∀ k : Fin 60, ∃ a b c d : Bool,
    gsub (gmul (transferCode i a b) (groupCode k c d))
      (gmul (transferCode i c d) (groupCode k a b))≠gz := by
  intro i
  fin_cases i <;> decide +kernel

end Golden
end Holant.Certificates.PlatonicQuaternaryExits.Deficient
