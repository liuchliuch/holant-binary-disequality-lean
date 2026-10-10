import Holant.Certificates.FourthRootOdd.Source

/-! Exact raw scalars for the literal constructions. Normalizing the input
does not silently identify its raw one-copy/two-copy output with the normalized
table: the multipliers are c and c² respectively. -/
namespace Holant.Certificates.FourthRootOdd
open Holant
variable {K : Type*} [CommSemiring K]

theorem nativeContract_scale (c : K) (f : Signature K 4) (p : Fin 6) :
    nativeContract (fun x => c*f x) p=fun x => c*nativeContract f p x := by
  funext x
  simp [nativeContract,Signature.contract_disequality,Tensor.reindex,mul_add]

theorem equalityContract_scale (c : K) (f : Signature K 4) (p : Fin 6) :
    equalityContract (fun x => c*f x) p=fun x => c*equalityContract f p x := by
  funext x
  simp [equalityContract,Signature.contract_equality,Tensor.reindex,mul_add]

theorem twoCopyNative_scale (c : K) (f : Signature K 4) (p : Fin 6) :
    twoCopyNative (fun x => c*f x) p=fun x => c^2*twoCopyNative f p x := by
  rw [twoCopyNative_eq,twoCopyNative_eq]
  funext x
  simp [twoCopy,Finset.mul_sum]
  ring

end Holant.Certificates.FourthRootOdd
