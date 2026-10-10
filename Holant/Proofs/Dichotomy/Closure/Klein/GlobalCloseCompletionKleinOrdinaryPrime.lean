import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryPair
import Holant.Certificates.EqualityQuaternary.Primality

/-! Genuine tensor primality forces the ordinary pair matrix determinant to
be nonzero. The excluded case is factored across the explicit original pair
partition, including its zero-coefficient boundary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryPrime
open Holant Holant.Tractable
open Holant.Certificates.EqualityQuaternary
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric)
end P
namespace M
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneChain (binary bitIndex)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem factor_of_square (a d : AlgebraicComplex) (square : a^2=d^2) :
    ProperFactor (P.pair (M.binary (P.symmetric a d))) := by
  by_cases ha : a=0
  · have hd : d=0 := (pow_eq_zero_iff (by decide : 2≠0)).mp (by simpa [ha] using square.symm)
    subst a; subst d
    refine ⟨2,2,by decide,by decide,finSumFinEquiv,(0 : Signature AlgebraicComplex 2),
      (0 : Signature AlgebraicComplex 2),?_⟩
    funext x
    cases h0 : x 0 <;> cases h2 : x 2 <;>
      simp [P.pair,M.binary,M.bitIndex,P.symmetric,Tensor.reindex,Tensor.tensor,h0,h2]
  · let f : Signature AlgebraicComplex 2 := fun x=>if x 0=x 1 then (if x 0 then d else a) else 0
    let g : Signature AlgebraicComplex 2 := fun x=>if x 0=x 1 then (if x 0 then d/a else 1) else 0
    refine ⟨2,2,by decide,by decide,finSumFinEquiv,f,g,?_⟩
    funext x
    change P.pair (M.binary (P.symmetric a d)) x=
      f (fun i=>x (Fin.castAdd 2 i))*g (fun i=>x (Fin.natAdd 2 i))
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [P.pair,M.binary,M.bitIndex,P.symmetric,f,g,h0,h1,h2,h3] <;>
      field_simp [ha] <;> linear_combination square

theorem prime_separated (a d : AlgebraicComplex)
    (prime : TensorPrime (P.pair (M.binary (P.symmetric a d)))) : a^2≠d^2 :=
  fun square=>prime.2 (factor_of_square a d square)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinOrdinaryPrime
end
