import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryExoticEq4
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned

/-! Exact weighted antidiagonal in the exotic Hadamard dictionary. Its ratio
squares to -1 and its fourth powers agree; the eighth-power-failure terminal
is therefore intentionally not applicable. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticAntiAlgebra
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Certificates.EqualityQuaternary
namespace A
export GlobalCloseCompletionKleinOrdinaryAttach (binary)
end A
namespace T
export GlobalCloseCompletionKleinOrdinaryHTransport (H)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def left (c : AlgebraicComplex) : AlgebraicComplex := c*(imaginaryUnit-1)/2
def right (c : AlgebraicComplex) : AlgebraicComplex := c*(imaginaryUnit+1)/2

theorem literal (c : AlgebraicComplex) :
    A.binary (transport T.H (scale c (Klein.E .exotic 2)))=
      NoXWeightedAntiSigned.anti (left c) (right c) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [A.binary,transport,T.H,GlobalCloseCompletionKleinBAlgebra.H,
      GlobalCloseCompletionKleinHadamardAlgebra.H,basisA,UAInv,
      Kernel.mul_apply,Kernel.transpose,scale,Klein.E,Klein.basisQ,Klein.matrix,Klein.embed_apply,Klein.qI,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,
      NoXWeightedAntiSigned.anti,left,right,h0,h1] <;> ring

theorem squares (c : AlgebraicComplex) : (left c)^2= -(right c)^2 := by
  simp only [left,right]
  ring_nf
  simp [imaginaryUnit_sq]

theorem right_nonzero (c : AlgebraicComplex) (hc : c≠0) : right c≠0 := by
  apply div_ne_zero _ (by norm_num)
  apply mul_ne_zero hc
  intro hz
  have hi : imaginaryUnit=(-1 : AlgebraicComplex) := add_eq_zero_iff_eq_neg.mp hz
  have hs := imaginaryUnit_sq
  rw [hi] at hs
  norm_num at hs

theorem left_nonzero (c : AlgebraicComplex) (hc : c≠0) : left c≠0 := by
  intro zero
  have hs := squares c
  rw [zero,zero_pow (by decide : 2≠0)] at hs
  have h := neg_eq_zero.mp hs.symm
  exact right_nonzero c hc ((pow_eq_zero_iff (by decide : 2≠0)).mp h)

theorem fourths (c : AlgebraicComplex) : (left c)^4=(right c)^4 := by
  calc
    (left c)^4=((left c)^2)^2 := by ring
    _= (-(right c)^2)^2 := by rw [squares]
    _=(right c)^4 := by ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticAntiAlgebra
end
