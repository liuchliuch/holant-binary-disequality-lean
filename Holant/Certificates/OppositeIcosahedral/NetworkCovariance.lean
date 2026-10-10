import Holant.Certificates.OppositeIcosahedral.DiagonalTransport
import Holant.Network

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Reindex the actual incidence bijection, so every boundary and every internal
endpoint occurrence is counted once, including loops and parallel edges. -/
theorem network_port_weights {n : ℕ} (s : NetworkShape n) (x : Fin n→Bool)
    (z : (Fin s.edges×Bool)→Bool) :
    (∏v,weight (s.assignment x z v))=weight x*
      ∏e,diagonalWeight (z (e,false))*diagonalWeight (z (e,true)) := by
  classical
  let W : Fin n⊕(Fin s.edges×Bool)→ℂ := Sum.elim
    (fun j => diagonalWeight (x j)) (fun eb => diagonalWeight (z eb))
  have hp (p : (Σv : Fin s.vertices,Fin (s.arity v))) :
      diagonalWeight (s.assignment x z p.1 p.2)=W (s.ports p) := by
    cases he : s.ports p <;> simp [NetworkShape.assignment,he,W]
  simp only [weight]
  rw [←Fintype.prod_sigma (fun p : (Σv : Fin s.vertices,Fin (s.arity v)) =>
    diagonalWeight (s.assignment x z p.1 p.2))]
  simp_rw [hp]
  rw [s.ports.prod_comp]
  simp [W,Fintype.prod_sum_type,Fintype.prod_prod_type,Fintype.prod_bool,mul_comm]

theorem kappa_endpoint_cancel (K : Mat) (a b : Bool) :
    (diagonalWeight a*diagonalWeight b)*kappa K a b=K a b := by
  cases a <;> cases b <;>
    simp [diagonalWeight,kappa,Dinv,Q0,Q3,Signature.equality,Matrix.mul_apply,Matrix.smul_apply] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

def oppositeNetwork {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (E : Fin s.edges→Mat) : Network ℂ n :=
  ⟨s,f,fun e => kappa (E e)⟩

def analyticalNetwork {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (E : Fin s.edges→Mat) : Network ℂ n :=
  ⟨s,fun v => analytical (f v),E⟩

/-- Full open-network covariance of the literal finite assignment sum. The left
network keeps every original vertex signature and only uses actual κ-kernels.
The analytical vertex tuple appears solely on the right side of this identity. -/
theorem network_covariance {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (E : Fin s.edges→Mat) :
    (oppositeNetwork s f E).denote=transport (analyticalNetwork s f E).denote := by
  classical
  have hv (v : Fin s.vertices) : f v=transportTensor (analytical (f v)) := by
    rw [←transport_eq_tensor,transport_analytical]
  funext x
  rw [transport_eq_tensor]
  change (∑z,(∏v,f v (s.assignment x z v))*∏e,kappa (E e) (z (e,false)) (z (e,true)))=
    weight x*(∑z,(∏v,analytical (f v) (s.assignment x z v))*∏e,E e (z (e,false)) (z (e,true)))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  conv_lhs => arg 1; arg 2; ext v; rw [hv v]
  simp only [transportTensor,Finset.prod_mul_distrib]
  rw [network_port_weights]
  have he : (∏e,diagonalWeight (z (e,false))*diagonalWeight (z (e,true)))*
      (∏e,kappa (E e) (z (e,false)) (z (e,true)))=
      ∏e,E e (z (e,false)) (z (e,true)) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro e he
    exact kappa_endpoint_cancel (E e) _ _
  calc
    _=weight x*(∏v,analytical (f v) (s.assignment x z v))*
      ((∏e,diagonalWeight (z (e,false))*diagonalWeight (z (e,true)))*
       ∏e,kappa (E e) (z (e,false)) (z (e,true))) := by ring
    _=_ := by rw [he]; ring

theorem edge_scalars {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (E : Fin s.edges→Mat) (c : Fin s.edges→ℂ) :
    (Network.mk s f (fun e => c e • E e)).denote=(∏e,c e) • (Network.mk s f E).denote := by
  funext x
  simp only [Network.denote,Matrix.smul_apply,smul_eq_mul,Pi.smul_apply,Finset.prod_mul_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z hz
  ring

/-- Literal fixed opposite representatives retain every edge scalar separately. -/
theorem fixed_network_covariance {n : ℕ} (s : NetworkShape n)
    (f : (v : Fin s.vertices)→Signature ℂ (s.arity v)) (i : Fin s.edges→Fin 60) :
    (Network.mk s f (fun e => oppositeRepresentative (kernelIndex (i e)))).denote=
      (∏e,(kernelScale (i e))⁻¹) • transport (analyticalNetwork s f (fun e => standardRepresentative (i e))).denote := by
  have he (e : Fin s.edges) : oppositeRepresentative (kernelIndex (i e))=
      (kernelScale (i e))⁻¹ • kappa (standardRepresentative (i e)) := by
    rw [kernel_representative_exact,smul_smul,inv_mul_cancel₀ (kernelScale_ne_zero (i e)),one_smul]
  simp_rw [he]
  rw [edge_scalars]
  congr 1
  exact network_covariance s f (fun e => standardRepresentative (i e))

theorem network_scale_ne_zero {m : ℕ} (i : Fin m→Fin 60) : (∏e,(kernelScale (i e))⁻¹)≠0 :=
  Finset.prod_ne_zero_iff.mpr (fun e _ => inv_ne_zero (kernelScale_ne_zero (i e)))

end
end Holant.Certificates.OppositeIcosahedral
