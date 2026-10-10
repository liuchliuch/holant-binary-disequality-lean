import Holant.Dihedral.EndpointSaturation.Cosets

/-! Full endpoint supports are derived from their literal nonzero coefficient
products. A point on the designated edge and nonzero monomial entries on each
fixed edge provide exactly one product coefficient, with no cancellation. -/
noncomputable section
namespace Holant.Dihedral.EndpointSaturation
open Holant Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {r n : ℕ}

 def endpointProduct (p : (Fin r × Bool) ≃ Fin n) (e : Fin r)
    (α : Fin r → ZMod 2) (w : Fin r → Bool → K) (κ : K) (a b : ZMod 2) : Signature K n := fun x =>
  κ*(∏ j ∈ Finset.univ.erase e,
      if bitEquiv (x (p (j,true)))=bitEquiv (x (p (j,false)))+α j then w j (x (p (j,false))) else 0)*
    (if bitEquiv (x (p (e,false)))=a ∧ bitEquiv (x (p (e,true)))=b then 1 else 0)

 theorem endpointProduct_full (p : (Fin r × Bool) ≃ Fin n) (e : Fin r)
    (α : Fin r → ZMod 2) (w : Fin r → Bool → K) (κ : K) (a b : ZMod 2)
    (hw : ∀ j,j ≠ e → ∀ z,w j z ≠ 0) (hκ : κ ≠ 0) :
    fullCoset (fun x => endpointProduct p e α w κ a b ((bitsEquiv (Fin n)).symm x))
      (fixedCode p e) (endpointOffset p e α a b) := by
  classical
  intro x
  rw [fixed_coset_iff]
  have hb (i : Fin n) : bitEquiv ((bitsEquiv (Fin n)).symm x i)=x i :=
    bitEquiv.apply_symm_apply _
  simp only [endpointProduct,hb,mul_ne_zero_iff,hκ,true_and,
    Finset.prod_ne_zero_iff,Finset.mem_erase,Finset.mem_univ,and_true]
  have he (j : Fin r) (hj : j ≠ e) :
      (if x (p (j,true))=x (p (j,false))+α j
        then w j ((bitsEquiv (Fin n)).symm x (p (j,false))) else 0) ≠ 0 ↔
      x (p (j,true))=x (p (j,false))+α j := by
    by_cases hh : x (p (j,true))=x (p (j,false))+α j <;> simp [hh,hw j hj]
  have hp : (if x (p (e,false))=a ∧ x (p (e,true))=b then (1:K) else 0) ≠ 0 ↔
      x (p (e,false))=a ∧ x (p (e,true))=b := by simp
  rw [hp]
  constructor
  · rintro ⟨⟨_,hprod⟩,hpoint⟩
    exact ⟨hpoint.1,hpoint.2,fun j hj => (he j hj).mp (hprod j hj)⟩
  · rintro ⟨ha,hb,hprod⟩
    exact ⟨⟨hκ,fun j hj => (he j hj).mpr (hprod j hj)⟩,ha,hb⟩

 theorem endpointProduct_nonzero (p : (Fin r × Bool) ≃ Fin n) (e : Fin r)
    (α : Fin r → ZMod 2) (w : Fin r → Bool → K) (κ : K) (a b : ZMod 2)
    (hw : ∀ j,j ≠ e → ∀ z,w j z ≠ 0) (hκ : κ ≠ 0) :
    endpointProduct p e α w κ a b ≠ 0 := by
  intro hz
  have hh := endpointProduct_full p e α w κ a b hw hκ (endpointOffset p e α a b)
  have hn := hh.mpr (by simp [coset,ZModModule.add_self])
  exact hn (congrFun hz _)

end Holant.Dihedral.EndpointSaturation
