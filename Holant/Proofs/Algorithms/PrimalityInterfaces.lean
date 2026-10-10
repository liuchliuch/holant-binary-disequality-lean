import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange
import Holant.Proofs.Algorithms.CyclicBoundary.C2Bridge
import Holant.Proofs.Algorithms.CyclicBoundary.CoordinateFactors
import Holant.Proofs.Algorithms.RingHomRealization


namespace Holant.LocalDrafts.MainChain.PrimalityInterfaces
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem retained_equality_prime (q : Signature AlgebraicComplex 4) :
    Holant.LocalDrafts.FinitePGL2.Stabilization.Prime (⟨4,q⟩ : AnySignature AlgebraicComplex) ↔ Holant.Certificates.EqualityQuaternary.TensorPrime q := by
  constructor
  · rintro ⟨hn,hp⟩
    refine ⟨hn,?_⟩
    rintro ⟨m,n,hm,hn',p,f,g,he⟩
    exact hp ⟨⟨m,f⟩,⟨n,g⟩,⟨{
      left_pos:=hm,right_pos:=hn',ports:=p,scale:=1,
      equation:=by
        funext x
        exact (congrFun he x).trans (one_mul _).symm}⟩⟩
  · rintro ⟨hn,hp⟩
    refine ⟨hn,?_⟩
    rintro ⟨a,b,⟨s⟩⟩
    refine hp ⟨a.1,b.1,s.left_pos,s.right_pos,s.ports,(s.scale:AlgebraicComplex) • a.2,b.2,?_⟩
    funext x
    have h := congrFun s.equation x
    simpa only [Tensor.reindex,Tensor.tensor,Pi.smul_apply,smul_eq_mul,mul_assoc] using h

theorem retained_complex_prime {n : ℕ} (q : Signature ℂ n) :
    Holant.LocalDrafts.FinitePGL2.Stabilization.Prime (⟨n,q⟩ : AnySignature ℂ) ↔ q≠0 ∧ ¬Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor q := by
  constructor
  · rintro ⟨hn,hp⟩
    refine ⟨hn,?_⟩
    rintro ⟨m,k,hm,hk,p,f,g,hf,hg,he⟩
    exact hp ⟨⟨m,f⟩,⟨k,g⟩,⟨{
      left_pos:=hm,right_pos:=hk,ports:=p,scale:=1,
      equation:=by
        funext x
        exact (congrFun he x).trans (one_mul _).symm}⟩⟩
  · rintro ⟨hn,hp⟩
    refine ⟨hn,?_⟩
    rintro ⟨a,b,⟨s⟩⟩
    have hab := s.factors_nonzero hn
    refine hp ⟨a.1,b.1,s.left_pos,s.right_pos,s.ports,(s.scale:ℂ) • a.2,b.2,
      smul_ne_zero s.scale.ne_zero hab.1,hab.2,?_⟩
    funext x
    have h := congrFun s.equation x
    simpa only [Tensor.reindex,Tensor.tensor,Pi.smul_apply,smul_eq_mul,mul_assoc] using h

theorem embedded_prime {L : Type*} [Field L] (φ : L →+* ℂ)
    {n : ℕ} (q : Signature L n) (hq : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime (⟨n,q⟩ : AnySignature L)) :
    RingHomRealization.mapSignature φ q ≠ 0 ∧
      ¬Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor (RingHomRealization.mapSignature φ q) := by
  apply (retained_complex_prime _).mp
  exact (Holant.LocalDrafts.FinitePGL2.Stabilization.prime_mapSignature_iff φ ⟨n,q⟩).mpr hq

theorem equality_prime_embedded (q : Signature AlgebraicComplex 4) (hq : Holant.Certificates.EqualityQuaternary.TensorPrime q) :
    (fun x => (q x : ℂ)) ≠ 0 ∧ ¬Holant.Pauli.ExoticKlein.Fiber.HasProperTensorFactor (fun x => (q x : ℂ)) :=
  by
    have h := embedded_prime (L := AlgebraicComplex) ((algebraicClosure ℚ ℂ).subtype) q
      ((retained_equality_prime q).mpr hq)
    exact h

end
end Holant.LocalDrafts.MainChain.PrimalityInterfaces
