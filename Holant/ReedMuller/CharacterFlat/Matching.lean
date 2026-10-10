import Holant.ReedMuller.CharacterFlat.Bell
import Holant.ReedMuller.CharacterFlat.Factors

/-! Every character on an actual matching coset splits into literal ordered
Bell factors, with the affine orientation signs carried by a nonzero scalar. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {r n : ℕ}

def characterWeight (ell : Character n) (i : Fin n) : ZMod 2 :=
  ell (fun j => if i=j then 1 else 0)

theorem character_expansion (ell : Character n) (x : BinaryVector n) :
    ell x=∑ i,characterWeight ell i*x i := by
  rw [LinearMap.pi_apply_eq_sum_univ]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem character_matching_expansion (M : Matching r n) (ell : Character n) (x : BinaryVector n) :
    ell x=∑ e,(characterWeight ell (M (e,0))*x (M (e,0))+
      characterWeight ell (M (e,1))*x (M (e,1))) := by
  rw [character_expansion,←M.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  exact Fin.sum_univ_two _

def matchingParity (M : Matching r n) (a : BinaryVector n) (e : Fin r) : ZMod 2 :=
  a (M (e,0))+a (M (e,1))
def matchingPhase (M : Matching r n) (ell : Character n) (e : Fin r) : ZMod 2 :=
  characterWeight ell (M (e,0))+characterWeight ell (M (e,1))
def matchingConstant (M : Matching r n) (a : BinaryVector n) (ell : Character n) : ZMod 2 :=
  ∑ e,characterWeight ell (M (e,1))*matchingParity M a e

theorem character_matching_phase (M : Matching r n) (a : BinaryVector n)
    (ell : Character n) (x : BinaryVector n) (hx : M.Holds (x-a)) :
    ell x=(∑ e,matchingPhase M ell e*x (M (e,0)))+matchingConstant M a ell := by
  rw [character_matching_expansion,matchingConstant,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hc : ∀ a b u v : ZMod 2,u-a=v-b → v=u+(a+b) := by decide
  have h := hc _ _ _ _ (hx e)
  dsimp only [matchingPhase,matchingParity]
  rw [h]
  ring

def bellDecomposition (M : Matching r n) (c : ℂˣ) (a : BinaryVector n) (ell : Character n) :
    TensorDecomposition ℂ n where
  count := r
  arity := fun _ => 2
  factor e := bellSignature (matchingParity M a e) (matchingPhase M ell e)
  ports := (Equiv.sigmaEquivProd (Fin r) (Fin 2)).trans M
  scale := c*Units.mk0 (sign (matchingConstant M a ell)) (sign_nonzero _)

 theorem bellDecomposition_value (M : Matching r n) (c : ℂˣ) (a : BinaryVector n)
    (D : BinaryCode n) (ell : Character n) (hD : ∀ x,x∈D ↔ M.Holds x) :
    (bellDecomposition M c a ell).value=signature c a D ell := by
  funext x
  have hc : ∀ a b : ZMod 2,∀ u v : Bool,
      (boolEquiv u+boolEquiv v=a+b) ↔ (bit u-a=bit v-b) := by decide
  change ((c:ℂ)*sign (matchingConstant M a ell))*
    (∏ e,sign (matchingPhase M ell e*bit (x (M (e,0))))*
      (if boolEquiv (x (M (e,0)))+boolEquiv (x (M (e,1)))=matchingParity M a e then 1 else 0))=_
  simp only [matchingParity,hc]
  rw [Finset.prod_mul_distrib,Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one,signature,value,hD,Matching.Holds]
  have hp : sign ((∑ e,matchingPhase M ell e*bit (x (M (e,0)))))=
      ∏ e,sign (matchingPhase M ell e*bit (x (M (e,0)))) := sign_finset_sum _ _
  rw [←hp]
  change ((c:ℂ)*sign (matchingConstant M a ell))*
    (sign (∑ e,matchingPhase M ell e*bit (x (M (e,0))))*
      (if ∀ e,bit (x (M (e,0)))-a (M (e,0))=bit (x (M (e,1)))-a (M (e,1)) then 1 else 0))=
    if ∀ e,bit (x (M (e,0)))-a (M (e,0))=bit (x (M (e,1)))-a (M (e,1))
    then (c:ℂ)*sign (ell (vectorWord x)) else 0
  by_cases h : M.Holds (vectorWord x-a)
  · have h' : ∀ e,bit (x (M (e,0)))-a (M (e,0))=bit (x (M (e,1)))-a (M (e,1)) := h
    simp only [if_pos h',mul_one]
    have he := character_matching_phase M a ell (vectorWord x) h
    rw [he,sign_add]
    have hv : vectorWord x=(fun i => bit (x i)) := rfl
    rw [hv]
    ring
  · have h' : ¬∀ e,bit (x (M (e,0)))-a (M (e,0))=bit (x (M (e,1)))-a (M (e,1)) := h
    simp only [if_neg h',mul_zero]

/-- Item 3 includes the empty matching at arity zero. -/
theorem low_arity_character_matching (r : ℕ) (hr : r≤3) (f : Signature ℂ (2*r))
    (hf : NonzeroFlat f) :
    ∃ (M : Matching r (2*r)) (c : ℂˣ) (a : BinaryVector (2*r)) (ell : Character (2*r)),
      (bellDecomposition M c a ell).value=f := by
  obtain ⟨c,a,D,ell,hD,rfl⟩ := hf
  obtain ⟨M,hM⟩ := low_arity_matching r hr D hD
  exact ⟨M,c,a,ell,bellDecomposition_value M c a D ell hM⟩

end
end Holant.ReedMuller.CharacterFlat
