import Holant.Platonic.FixedMatchingRuling.SegreCoordinates

/-! Projective equality of literal nonzero products recovers all individual
factor scales, including their exact product. -/
namespace Holant.Platonic.RainbowLocalization
noncomputable section
open scoped BigOperators
open Function
variable {E : Type*} [Fintype E] [DecidableEq E] {α : E→Type*}

 def factorCofactor (U : ∀e,α e→ℂ) (x : ∀e,α e) (e : E) : ℂ :=
  ∏i : {i : E // i≠e},U i.val (x i.val)

 theorem product_update_coordinate (U : ∀e,α e→ℂ) (x : ∀e,α e)
    (e : E) (z : α e) :
    (∏i,U i (update x e z i))=U e z*factorCofactor U x e := by
  rw [Fintype.prod_eq_mul_prod_compl e]
  simp only [update_self,factorCofactor]
  congr 1
  rw [Finset.prod_subtype (p:=fun i : E=>i≠e) {e}ᶜ (by intro i;simp)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [update_of_ne i.property]

 theorem factor_scale_of_product_equality (U V : ∀e,α e→ℂ) (c : ℂ) (hc : c≠0)
    (hV : (fun x : ∀e,α e=>∏i,V i (x i))≠0)
    (h : ∀x : ∀e,α e,(∏i,U i (x i))=c*(∏i,V i (x i))) (e : E) :
    ∃s : ℂ,s≠0 ∧ ∀z,U e z=s*V e z := by
  classical
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hV
  have hv : (∏i,V i (x i))≠0 := hx
  have hu : (∏i,U i (x i))≠0 := by rw [h];exact mul_ne_zero hc hv
  have hv' : ∀i,V i (x i)≠0 := fun i=>Finset.prod_ne_zero_iff.mp hv i (Finset.mem_univ i)
  have hu' : ∀i,U i (x i)≠0 := fun i=>Finset.prod_ne_zero_iff.mp hu i (Finset.mem_univ i)
  have hcu : factorCofactor U x e≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _=>hu' i.val)
  have hcv : factorCofactor V x e≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _=>hv' i.val)
  refine ⟨c*factorCofactor V x e/factorCofactor U x e,div_ne_zero (mul_ne_zero hc hcv) hcu,?_⟩
  intro z
  have hz := h (update x e z)
  rw [product_update_coordinate,product_update_coordinate] at hz
  apply (mul_right_cancel₀ hcu)
  calc
    U e z*factorCofactor U x e=c*(V e z*factorCofactor V x e) := hz
    _=(c*factorCofactor V x e/factorCofactor U x e*V e z)*factorCofactor U x e := by
      field_simp

 theorem product_factor_projective_scales (U V : ∀e,α e→ℂ) (c : ℂ) (hc : c≠0)
    (hV : (fun x : ∀e,α e=>∏i,V i (x i))≠0)
    (h : ∀x : ∀e,α e,(∏i,U i (x i))=c*(∏i,V i (x i))) :
    ∃s : E→ℂ,(∀e,s e≠0) ∧ (∀e z,U e z=s e*V e z) ∧ (∏e,s e)=c := by
  classical
  choose s hs he using fun e=>factor_scale_of_product_equality U V c hc hV h e
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hV
  refine ⟨s,hs,he,?_⟩
  have hh := h x
  simp_rw [he] at hh
  rw [Finset.prod_mul_distrib] at hh
  exact mul_right_cancel₀ hx hh

end
end Holant.Platonic.RainbowLocalization
