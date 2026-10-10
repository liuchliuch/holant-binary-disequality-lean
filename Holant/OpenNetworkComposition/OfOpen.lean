import Holant.OpenNetworkComposition.Semantics

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.FiniteNetwork
variable {K : Type*} {n : ℕ} [CommSemiring K]

private theorem sum_instances {A : Type*} (I J : Fintype A) (f g : A → K) (h : ∀a,f a=g a) :
    (@Finset.univ A I).sum f=(@Finset.univ A J).sum g := by
  have he : I=J := Subsingleton.elim _ _
  cases he
  exact Finset.sum_congr rfl (fun a _ => h a)

@[simp] theorem ofOpen_tensor (N : OpenNetwork K n) : (ofOpen N).tensor=N.tensor := by
  have hb : (ofOpen N).boundaryKernel=N.boundaryKernel := by
    funext j
    cases h : N.shape.boundary j <;>
      simp [boundaryKernel,OpenNetwork.boundaryKernel,ofOpen,h]
  have hr : (ofOpen N).raw=N.raw := by
    classical
    funext x
    dsimp only [ofOpen,raw,OpenNetwork.raw]
    apply sum_instances
    intro z
    split_ifs <;> rfl
  rw [tensor,hb,hr]
  rfl

end Holant.OpenNetworkComposition.FiniteNetwork
