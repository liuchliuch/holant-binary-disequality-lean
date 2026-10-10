import Holant.Certificates.OppositeIcosahedral.NetworkCovariance

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem kappa_X : kappa X=(1/2 : ℂ) • X := by
  ext a b
  cases a <;> cases b <;>
    simp [kappa,Dinv,X,Q0,Q3,Signature.equality,Signature.disequality,Matrix.mul_apply,Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> norm_num

/-- Keeping every native-X edge literal, rather than replacing it by κ(X),
contributes exactly two per original edge, including closed components. -/
theorem native_network_scalar {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) :
    (Network.mk s f (fun _ => X)).denote=(2 : ℂ)^s.edges •
      transport (analyticalNetwork s f (fun _ => X)).denote := by
  have hk : X=(2 : ℂ) • kappa X := by rw [kappa_X,smul_smul]; norm_num
  have he : Network.mk s f (fun _ => X)=Network.mk s f (fun _ => (2 : ℂ) • kappa X) := by
    congr 1
    funext e
    exact hk
  rw [he,edge_scalars]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  exact network_covariance s f (fun _ => X)

theorem native_network_scalar_ne_zero (m : ℕ) : (2 : ℂ)^m≠0 := pow_ne_zero _ (by norm_num)

end
end Holant.Certificates.OppositeIcosahedral
