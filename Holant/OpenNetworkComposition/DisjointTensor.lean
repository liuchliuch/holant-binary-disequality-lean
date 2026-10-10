import Holant.OpenNetworkComposition.DisjointTensorSemantics
import Holant.OpenNetworkComposition.OfOpen

/-! Disjoint tensor closure of actual full open gadgets, with exact scalars,
ordinary and free boundaries, arbitrary arities, and either native edge kind. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition
namespace DisjointTensor
variable {K VL VR FL FR EL ER : Type*} {m n : ℕ}
variable [Fintype VL] [Fintype VR] [Fintype FL] [Fintype FR] [Fintype EL] [Fintype ER] [CommSemiring K]

theorem realizes_network (L : FiniteNetwork K VL FL EL m) (R : FiniteNetwork K VR FR ER n)
    (family : SignatureFamily K) (W : EdgeKind)
    (vL : ∀v,(⟨L.shape.arity v,L.vertex v⟩ : AnySignature K)∈family)
    (vR : ∀v,(⟨R.shape.arity v,R.vertex v⟩ : AnySignature K)∈family)
    (eL : ∀e,L.edge e=W) (eR : ∀e,R.edge e=W) :
    Gadget.Realizes family W (Signature.tensor L.tensor R.tensor) := by
  rw [←network_tensor L R W eL eR]
  apply FiniteNetwork.realizes
  · rintro (v|v)
    · exact vL v
    · exact vR v
  · exact network_edges L R W eL eR

end DisjointTensor
variable {K : Type*} [CommSemiring K] {m n : ℕ}

/-- Arbitrary supplied gadgets can be tensored exactly, with complete left
boundary first and complete right boundary second. Free stubs remain explicit. -/
theorem realizes_tensor (family : SignatureFamily K) (W : EdgeKind)
    (f : Signature K m) (g : Signature K n)
    (hf : Gadget.Realizes family W f) (hg : Gadget.Realizes family W g) :
    Gadget.Realizes family W (Signature.tensor f g) := by
  obtain ⟨L,vL,eL,hL⟩ := hf
  obtain ⟨R,vR,eR,hR⟩ := hg
  have H := DisjointTensor.realizes_network (FiniteNetwork.ofOpen L) (FiniteNetwork.ofOpen R)
    family W vL vR eL eR
  rw [FiniteNetwork.ofOpen_tensor,FiniteNetwork.ofOpen_tensor,hL,hR] at H
  exact H

theorem tensor_scale (c d : K) (f : Signature K m) (g : Signature K n) :
    Signature.tensor (fun x => c*f x) (fun x => d*g x)=fun x => (c*d)*Signature.tensor f g x := by
  funext x
  simp only [Signature.tensor_apply]
  ac_rfl

/-- Projective disjoint union multiplies the two original nonzero scalars. -/
theorem realizesUpTo_tensor [NoZeroDivisors K] (family : SignatureFamily K) (W : EdgeKind)
    (f : Signature K m) (g : Signature K n)
    (hf : Gadget.RealizesUpTo family W f) (hg : Gadget.RealizesUpTo family W g) :
    Gadget.RealizesUpTo family W (Signature.tensor f g) := by
  obtain ⟨c,hc,hf⟩ := hf
  obtain ⟨d,hd,hg⟩ := hg
  refine ⟨c*d,mul_ne_zero hc hd,?_⟩
  have H := realizes_tensor family W _ _ hf hg
  rwa [tensor_scale] at H

end Holant.OpenNetworkComposition
