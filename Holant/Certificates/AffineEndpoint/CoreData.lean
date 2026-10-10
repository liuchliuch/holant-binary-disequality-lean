import Holant.Certificates.AffineEndpoint.Scalars
import Holant.Certificates.OctahedralSeparator.MatrixSemantics

/-! The literal eighteen A.4 coefficient cores, in the original ordered basis. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable Holant.Certificates.OctahedralSeparator
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

abbrev CoreIndex := Fin 2 ⊕ (Fin 8 ⊕ (Fin 4 × Bool))

 def coreRaw : CoreIndex → Mat
  | .inl j => if j=0 then q 0 else flip
  | .inr (.inl k) => mat 1 (rawZetaEight^k.val) 1 (-(rawZetaEight^k.val))
  | .inr (.inr (k,b)) =>
      let s := if b then -root else root
      mat 1 (imag^k.val*(1+s)) 1 (imag^k.val*(1-s))

 theorem core_index_card : Fintype.card CoreIndex=18 := by
  simp [CoreIndex]

 theorem coreRaw_injective : Function.Injective coreRaw := by decide +kernel
 theorem coreRaw_nonsingular : ∀k,determinant (coreRaw k)≠0 := by decide +kernel

end Holant.Certificates.AffineEndpoint
