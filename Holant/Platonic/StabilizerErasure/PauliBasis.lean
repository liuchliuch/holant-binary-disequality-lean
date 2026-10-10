import Holant.Platonic.StabilizerErasure.SingleSite

/-! The source's Hermitian representatives I, X, -iY, Z, with Y = ZX.
These span every one-qubit operator, so their scalar tests are exactly KL. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

def qubitPauli : Fin 4 → Bool → Bool → ℂ
  | 0 => fun u v => if u=v then 1 else 0
  | 1 => fun u v => if u≠v then 1 else 0
  | 2 => fun u v => if u=v then 0 else if u then Complex.I else -Complex.I
  | 3 => fun u v => if u=v then if u then -1 else 1 else 0

def pauliCoefficient (R : Bool → Bool → ℂ) : Fin 4 → ℂ :=
  ![(R false false+R true true)/2,(R false true+R true false)/2,
    Complex.I*(R false true-R true false)/2,(R false false-R true true)/2]

theorem qubitPauli_expansion (R : Bool → Bool → ℂ) (u v : Bool) :
    R u v=∑p : Fin 4,pauliCoefficient R p*qubitPauli p u v := by
  cases u <;> cases v <;>
    simp [pauliCoefficient,qubitPauli,Fin.sum_univ_succ] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem siteAction_pauli_expansion (r : Fin (n+1)) (R : Bool → Bool → ℂ)
    (f : Signature ℂ (n+1)) :
    siteAction r R f=∑p : Fin 4,pauliCoefficient R p • siteAction r (qubitPauli p) f := by
  ext w
  change (∑b : Bool,R (w r) b*f (r.insertNth b (r.removeNth w)))=_
  simp_rw [qubitPauli_expansion R,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,siteAction,
    LinearMap.coe_mk,AddHom.coe_mk,Finset.mul_sum,mul_assoc]

theorem correctable_iff_paulis (V : StabilizerIsometry k (n+1)) (r : Fin (n+1)) :
    Correctable V r ↔
      ∀p : Fin 4,IsScalar (fun f => V.adjoint (siteAction r (qubitPauli p) (V.map f))) := by
  constructor
  · intro h p;exact h (qubitPauli p)
  · intro h R
    choose a ha using h
    refine ⟨∑p : Fin 4,pauliCoefficient R p*a p,?_⟩
    intro f
    change V.adjoint (siteAction r R (V.map f))=_
    rw [siteAction_pauli_expansion]
    simp only [map_sum,map_smul]
    simp_rw [ha,smul_smul]
    rw [Finset.sum_smul]

theorem siteAction_qubitPauli_zero (r : Fin (n+1)) (f : Signature ℂ (n+1)) :
    siteAction r (qubitPauli 0) f=f := by
  ext w
  cases hw : w r <;> simp [siteAction,qubitPauli,hw]

theorem siteAction_qubitPauli_involution (r : Fin (n+1)) (p : Fin 4)
    (f : Signature ℂ (n+1)) :
    siteAction r (qubitPauli p) (siteAction r (qubitPauli p) f)=f := by
  ext w
  fin_cases p <;> cases hw : w r <;>
    simp [siteAction,qubitPauli,hw,←mul_assoc,Complex.I_mul_I]
  all_goals rw [←hw,Function.update_eq_self]

theorem not_correctable_pauli (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (h : ¬Correctable V r) :
    ∃p : Fin 4,p≠0 ∧ ¬IsScalar (fun f => V.adjoint (siteAction r (qubitPauli p) (V.map f))) := by
  have he : ¬∀p : Fin 4,IsScalar (fun f => V.adjoint (siteAction r (qubitPauli p) (V.map f))) :=
    fun he => h ((correctable_iff_paulis V r).mpr he)
  push_neg at he
  obtain ⟨p,hp⟩ := he
  refine ⟨p,?_,hp⟩
  rintro rfl
  apply hp
  refine ⟨1,?_⟩
  intro f
  simp [siteAction_qubitPauli_zero]

end
end Holant.Platonic.StabilizerErasure
