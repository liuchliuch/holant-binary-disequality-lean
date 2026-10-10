import Holant.OpenNetworkComposition.BoundarySums
import Holant.OpenNetworkComposition.FreeFreeTensor

/-! General boundary-correction calculation for one disjoint native-X splice.
The graph-specific hypotheses are an exact raw-sum law and preservation of the
remaining boundary kinds, not a gadget-closure assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.OpenNetworkComposition
namespace FiniteNetwork
variable {K V F E : Type*} {n : ℕ}

def flipBit (N : FiniteNetwork K V F E n) (j : Fin n) (a : Bool) : Bool :=
  match N.shape.boundary j with
  | .inl _ => a
  | .inr _ => !a

@[simp] theorem boundaryFlip_eq (N : FiniteNetwork K V F E n) (x : Fin n → Bool) (j : Fin n) :
    N.boundaryFlip x j=N.flipBit j (x j) := rfl

@[simp] theorem flipBit_involutive (N : FiniteNetwork K V F E n) (j : Fin n) (a : Bool) :
    N.flipBit j (N.flipBit j a)=a := by cases h : N.shape.boundary j <;> simp [flipBit,h]

end FiniteNetwork

variable {K VL FL EL VR FR ER VN FN EN : Type*} {n : ℕ}
variable [Fintype VL] [Fintype FL] [Fintype EL] [Fintype VR] [Fintype FR] [Fintype ER]
variable [Fintype VN] [Fintype FN] [Fintype EN] [CommSemiring K]
variable (L : FiniteNetwork K VL FL EL n) (R : FiniteNetwork K VR FR ER 2) (N : FiniteNetwork K VN FN EN n) (i : Fin n)
variable (away : ∀x j,j≠i → N.boundaryFlip x j=L.boundaryFlip x j)
variable (atPort : ∀x,N.boundaryFlip x i=R.flipBit 0 (x i))

include away in
theorem splice_flip_left (x : Fin n → Bool) (a : Bool) :
    L.boundaryFlip (Function.update x i a)=Function.update (N.boundaryFlip x) i (L.flipBit i a) := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · rw [Function.update_of_ne hj,away x j hj]
    simp only [FiniteNetwork.boundaryFlip_eq,Function.update_of_ne hj]

include atPort in
theorem splice_flip_right (x : Fin n → Bool) (b : Bool) :
    R.boundaryFlip (![x i,b])=![N.boundaryFlip x i,R.flipBit 1 b] := by
  funext j
  fin_cases j
  · exact (atPort x).symm
  · rfl

include away atPort in
/-- Boundary corrections cancel precisely the selected free-stub kernels.
This uniformly covers ordinary/ordinary, both mixed cases, and free/free. -/
theorem tensor_splice_of_raw
    (eL : ∀e,L.edge e=.disequality) (eR : ∀e,R.edge e=.disequality) (eN : ∀e,N.edge e=.disequality)
    (rawLaw : ∀x,N.raw x=∑a : Bool,∑b : Bool,L.raw (Function.update x i a)*R.raw (![x i,b])*
      Signature.disequality (L.flipBit i a) (R.flipBit 1 b)) :
    N.tensor=spliceTensor L.tensor R.tensor i := by
  funext x
  rw [N.tensor_eq_raw_boundaryFlip eN,rawLaw]
  unfold spliceTensor
  simp_rw [L.tensor_eq_raw_boundaryFlip eL,R.tensor_eq_raw_boundaryFlip eR,
    splice_flip_left L N i away,splice_flip_right R N i atPort]
  cases hL : L.shape.boundary i <;> cases hR : R.shape.boundary 1 <;>
    simp [FiniteNetwork.flipBit,hL,hR] <;> ac_rfl

end Holant.OpenNetworkComposition
