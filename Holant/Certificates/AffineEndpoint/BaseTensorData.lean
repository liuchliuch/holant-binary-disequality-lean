import Holant.Certificates.AffineEndpoint.IntegerValues
import Holant.Certificates.AffineEndpoint.CoreTensorData

/-! Small coefficient formulas for the two non-affine base cores. Their
identity to every original ordered tensor entry is checked separately. -/
namespace Holant.Certificates.AffineEndpoint
open Holant.Certificates.OctahedralSeparator IntegerValues

 def codeWeight : Fin 16 → Nat := ![0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]
 def codeIntersection (x y : Fin 16) : Fin 16 :=
  ⟨(x.val &&& y.val)%16,Nat.mod_lt _ (by decide)⟩
 def oddHadamardColumn : Nat → Coeff
  | 0 => ⟨4,0,0,0⟩
  | 1 => ⟨0,2,0,2⟩
  | 2 => ⟨0,0,4,0⟩
  | 3 => ⟨0,-2,0,2⟩
  | _ => ⟨-4,0,0,0⟩
 def mixedPower : Nat → Coeff
  | 0 => ⟨1,0,0,0⟩
  | 1 => ⟨1,1,0,0⟩
  | 2 => ⟨3,2,0,0⟩
  | 3 => ⟨7,5,0,0⟩
  | _ => ⟨17,12,0,0⟩
 def conjugateRoot (z : Coeff) : Coeff := ⟨z.a,-z.b,z.c,-z.d⟩
 def baseCore (b : Bool) : Fin 18 := if b then 10 else 3
 def baseTensor (b : Bool) (x y : Fin 16) : Coeff :=
  let t := codeWeight (codeIntersection x y)
  if b then IntegerCoefficient.mul (mixedPower (codeWeight y-t)) (conjugateRoot (mixedPower t)) else
    if t%2=0 then oddHadamardColumn (codeWeight y) else rotate (oddHadamardColumn (codeWeight y)) 2

end Holant.Certificates.AffineEndpoint
