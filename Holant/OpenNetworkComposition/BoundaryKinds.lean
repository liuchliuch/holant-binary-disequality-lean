import Holant.OpenNetworkComposition.TensorSplice
import Holant.OpenNetworkComposition.FreeFree
import Holant.OpenNetworkComposition.PortSum

/-! Boundary-kind transport through disjoint sums and deletion of another free
stub. These proofs inspect only ordinary/free tags, retaining exact port order. -/
noncomputable section
namespace Holant.OpenNetworkComposition

def portFlip {V F : Type*} {arity : V → ℕ} (p : Ports V F arity) (a : Bool) : Bool :=
  match p with | .inl _ => a | .inr _ => !a

theorem boundaryFlip_portFlip {K V F E : Type*} {n : ℕ}
    (N : FiniteNetwork K V F E n) (x : Fin n → Bool) (j : Fin n) :
    N.boundaryFlip x j=portFlip (N.shape.boundary j) (x j) := by
  cases hp : N.shape.boundary j <;> simp [FiniteNetwork.boundaryFlip,portFlip,hp]

theorem flipBit_portFlip {K V F E : Type*} {n : ℕ}
    (N : FiniteNetwork K V F E n) (j : Fin n) (a : Bool) :
    N.flipBit j a=portFlip (N.shape.boundary j) a := by
  cases hp : N.shape.boundary j <;> simp [FiniteNetwork.flipBit,portFlip,hp]

@[simp] theorem portFlip_left {VL VR FL FR : Type*} (aL : VL → ℕ) (aR : VR → ℕ)
    (p : Ports VL FL aL) (a : Bool) :
    portFlip (leftPort (FR := FR) aL aR p) a=portFlip p a := by cases p <;> rfl
@[simp] theorem portFlip_right {VL VR FL FR : Type*} (aL : VL → ℕ) (aR : VR → ℕ)
    (p : Ports VR FR aR) (a : Bool) :
    portFlip (rightPort (FL := FL) aL aR p) a=portFlip p a := by cases p <;> rfl
@[simp] theorem portFlip_sum_left {VL VR FL FR : Type*} (aL : VL → ℕ) (aR : VR → ℕ)
    (p : Ports VL FL aL) (a : Bool) :
    portFlip ((portSum (FR := FR) aL aR).symm (.inl p)) a=portFlip p a := by cases p <;> rfl
@[simp] theorem portFlip_sum_right {VL VR FL FR : Type*} (aL : VL → ℕ) (aR : VR → ℕ)
    (p : Ports VR FR aR) (a : Bool) :
    portFlip ((portSum (FL := FL) aL aR).symm (.inr p)) a=portFlip p a := by cases p <;> rfl

theorem portFlip_cut {V F E : Type*} {n : ℕ} (s : FiniteShape V F E n)
    (f : F) (p : s.CutPorts f) (a : Bool) : portFlip p a=portFlip (s.cutEmbed f p) a := by cases p <;> rfl

end Holant.OpenNetworkComposition
