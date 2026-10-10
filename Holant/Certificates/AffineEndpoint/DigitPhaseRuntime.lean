import Holant.Certificates.AffineEndpoint.PhaseCodes

/-! Small natural-number digit evaluation. Semantic equality to the intrinsic
ZMod4 quadratic is a separate theorem, not a change to the affine class. -/
namespace Holant.Certificates.AffineEndpoint.DigitPhaseRuntime

 def selectedDigits (base code mask : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => (if mask%2=1 then code%base else 0) + selectedDigits base (code/base) (mask/2) n

 def bit (y j : Nat) : Nat := if y.testBit j then 1 else 0

 def mixedMask (d y : Nat) : Nat :=
  if d=2 then bit y 0*bit y 1 else
  if d=3 then bit y 0*bit y 1+2*bit y 0*bit y 2+4*bit y 1*bit y 2 else
  if d=4 then bit y 0*bit y 1+2*bit y 0*bit y 2+4*bit y 0*bit y 3+
    8*bit y 1*bit y 2+16*bit y 1*bit y 3+32*bit y 2*bit y 3 else 0

 def exponent (d c y : Nat) : Nat :=
  (selectedDigits 4 (c/2^(d*(d-1)/2)) y d+
    2*selectedDigits 2 c (mixedMask d y) 6)%4

 theorem exponent_lt (d c y : Nat) : exponent d c y<4 := Nat.mod_lt _ (by decide)

end Holant.Certificates.AffineEndpoint.DigitPhaseRuntime
