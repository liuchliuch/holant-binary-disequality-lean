import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4IterationMachine
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4PassBounds
import Holant.Complexity.BinaryInterpolation.RingFormulaMachine
import Holant.Complexity.FixedGadgetSubstitution.Size

/-! Every stored outer-loop state has an explicit fixed-field byte bound.
The proof uses the actual suffix of roots processed by the controller and
the linear arithmetic budgets of the shrinking passes and denominator. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4IterationBounds
open Holant Holant.Algebraic Holant.Complexity Holant.OneHot
open BinaryCompose FixedFieldMachines GraphPreprocessing FixedGadgetSubstitution
namespace I
export GlobalCloseCompletionComplementQ4IterationMachine (State stateEncoding step fold_value)
end I
namespace P
export GlobalCloseCompletionComplementQ4PassBounds (foldr_bound foldr_length factor_bound)
end P
namespace D
export GlobalCloseCompletionComplementQ4Differences (pass factor)
end D
namespace R
export Holant.LocalDrafts.RemoteWork.RationalLP.Support.Infrastructure.ReverseFold
  (encoding tailEncoding start step iterate_start)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K A : Type} [Field K] [Algebra ℚ K] [Fintype A] {degree : ℕ}
variable (F : FixedField K degree) (coeff : A→Fin degree→ℚ)
variable (unit neg : A) (hone : F.decode (coeff unit)=1) (hneg : F.decode (coeff neg)= -1)

def width (D L R Y T E : ℕ) : ℕ:=
  2*((2*ArithmeticSize.bitBound F coeff R+2)*D+1)+2*D+
  2*((2*ArithmeticSize.bitBound F coeff (Y+D*(R+2))+2)*L+1)+
  2*ArithmeticSize.bitBound F coeff T+ArithmeticSize.bitBound F coeff (E+D*(T+R+2))+4

include hone hneg in
theorem stored_bound (roots values : List K) (target denominator : K)
    (d l r y t e : ℕ) (hd : roots.length≤d) (hl : values.length≤l)
    (hr : ∀x∈roots,ArithmeticSize.Bound (fun a=>F.decode (coeff a)) r x)
    (hv : ∀x∈values,ArithmeticSize.Bound (fun a=>F.decode (coeff a)) y x)
    (ht : ArithmeticSize.Bound (fun a=>F.decode (coeff a)) t target)
    (he : ArithmeticSize.Bound (fun a=>F.decode (coeff a)) e denominator) (k : ℕ) :
    ((R.encoding F.encoding (I.stateEncoding F)).encode
      (((R.step (0:K) I.step)^[k]) (R.start (roots,(values,(target,denominator)))))).length≤
      width F coeff d l r y t e := by
  rw [R.iterate_start,I.fold_value]
  let rest:=roots.drop (roots.length-k)
  have restLength : rest.length≤d:=by
    simp only [rest,List.length_drop]
    omega
  have restRoots : ∀x∈rest,ArithmeticSize.Bound (fun a=>F.decode (coeff a)) r x :=
    fun x hx=>hr x (List.mem_of_mem_drop hx)
  have newValues : ∀x∈rest.foldr D.pass values,
      ArithmeticSize.Bound (fun a=>F.decode (coeff a)) (y+d*(r+2)) x := by
    intro x hx
    exact (P.foldr_bound _ unit neg hone hneg rest values restRoots hv x hx).mono unit hone
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ restLength) _)
  have newDenominator : ArithmeticSize.Bound (fun a=>F.decode (coeff a)) (e+d*(t+r+2))
      (denominator*D.factor rest target) :=
    (he.mul (P.factor_bound _ unit neg hone hneg rest target restRoots ht)).mono unit hone
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ restLength) _)
  have rootBytes : ((framedListEncoding F.encoding).encode roots).length≤
      (2*ArithmeticSize.bitBound F coeff r+2)*d+1 := by
    exact (framedList_length_le F.encoding roots _ (fun x hx=>(hr x hx).encoded_length_le F coeff)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ hd) _)
  have valueLength : (rest.foldr D.pass values).length≤l:=(P.foldr_length rest values).trans hl
  have valueBytes : ((framedListEncoding F.encoding).encode (rest.foldr D.pass values)).length≤
      (2*ArithmeticSize.bitBound F coeff (y+d*(r+2))+2)*l+1 := by
    exact (framedList_length_le F.encoding _ _ (fun x hx=>(newValues x hx).encoded_length_le F coeff)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ valueLength) _)
  have targetBytes:=ht.encoded_length_le F coeff
  have denominatorBytes:=newDenominator.encoded_length_le F coeff
  have cursor : roots.length-k≤d:=Nat.sub_le _ _ |>.trans hd
  simp only [R.encoding,R.tailEncoding,I.stateEncoding,pairEncoding_length,
    GraphPreprocessing.UnaryBinary.unaryEncoding,List.length_replicate]
  change 2*((framedListEncoding F.encoding).encode roots).length+1+
    (2*(roots.length-k)+1+(2*((framedListEncoding F.encoding).encode (rest.foldr D.pass values)).length+1+
      (2*(F.encoding.encode target).length+1+(F.encoding.encode (denominator*D.factor rest target)).length)))≤_
  unfold width
  omega

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4IterationBounds
end
