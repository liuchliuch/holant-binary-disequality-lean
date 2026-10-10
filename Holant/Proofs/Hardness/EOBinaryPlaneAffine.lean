import Holant.Proofs.Hardness.EOBinaryPlaneProduct
import Holant.Tractable.AffinePhaseCriterion

/-! Exact full binary affine phase classification, independent of native
extraction and counted source programmes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
open Holant Holant.Tractable
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option Elab.async false

def SignedCross (f : Signature AlgebraicComplex 2) : Prop :=
  Cross f ∨ f ![false,false]*f ![true,true]=-(f ![false,true]*f ![true,false])

def CommonFourth (f : Signature AlgebraicComplex 2) : Prop :=
  ∀x,f x^4=f ![false,false]^4


theorem affine_signed_cross (f : Signature AlgebraicComplex 2) (hf : Full f) (h : Affine f) :
    SignedCross f := by
  have hh := AffinePhase.secondRatio_sq hf (AffinePhase.thirdTrivial_of_affine hf h)
    ![false,true] ![true,false]
  have hx : AffinePhase.xor (![false,true] : Fin 2→Bool) ![true,false]=![true,true] := by decide
  have ho : AffinePhase.origin 2=![false,false] := by decide
  simp only [AffinePhase.secondRatio,AffinePhase.origin_xor,hx] at hh
  rw [ho] at hh
  rw [div_pow,div_eq_one_iff_eq (pow_ne_zero 2 (mul_ne_zero (hf ![false,true]) (hf ![true,false])))] at hh
  rw [mul_comm (f ![true,true]) (f ![false,false])] at hh
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hh

/-- The finite mixed coefficient is exactly zero or two. -/
def phase (r s : ZMod 4) (minus : Bool) : QuadraticPhase 2 where
  constant := 0
  linear := ![r,s]
  mixed _ _ := if minus then 2 else 0
  even_mixed _ _ _ := by cases minus <;> simp

def formula (a : AlgebraicComplex) (r s : ZMod 4) (minus : Bool) : Signature AlgebraicComplex 2 :=
  affineFormula a (AffineSystem.unconstrained 2) (phase r s minus)

theorem formula_values (a : AlgebraicComplex) (r s : ZMod 4) (minus : Bool) :
    formula a r s minus ![false,false]=a ∧
    formula a r s minus ![false,true]=a*fourthRootPhase s ∧
    formula a r s minus ![true,false]=a*fourthRootPhase r ∧
    formula a r s minus ![true,true]=
      if minus then -(a*fourthRootPhase r*fourthRootPhase s) else a*fourthRootPhase r*fourthRootPhase s := by
  cases minus <;>
    simp [formula,affineFormula,phase,QuadraticPhase.eval,Fin.sum_univ_two,bitValue,fourthRootPhase_add,mul_assoc]

theorem affine_of_phases (f : Signature AlgebraicComplex 2) (ha : f ![false,false]≠0)
    (r s : ZMod 4) (minus : Bool)
    (hr : f ![false,false]*fourthRootPhase r=f ![true,false])
    (hs : f ![false,false]*fourthRootPhase s=f ![false,true])
    (hc : f ![false,false]*f ![true,true]=
      (if minus then -(f ![false,true]*f ![true,false]) else f ![false,true]*f ![true,false])) :
    Affine f := by
  have hv := formula_values (f ![false,false]) r s minus
  have hd : (if minus then -(f ![false,false]*fourthRootPhase r*fourthRootPhase s)
      else f ![false,false]*fourthRootPhase r*fourthRootPhase s)=f ![true,true] := by
    apply mul_left_cancel₀ ha
    cases minus
    · simp only [Bool.false_eq_true,ite_false] at hc ⊢
      calc
        _=(f ![false,false]*fourthRootPhase s)*(f ![false,false]*fourthRootPhase r) := by ring
        _=f ![false,true]*f ![true,false] := by rw [hr,hs]
        _=_ := hc.symm
    · simp only [ite_true] at hc ⊢
      calc
        _=-((f ![false,false]*fourthRootPhase s)*(f ![false,false]*fourthRootPhase r)) := by ring
        _=-(f ![false,true]*f ![true,false]) := by rw [hr,hs]
        _=_ := hc.symm
  have he : f=formula (f ![false,false]) r s minus := by
    funext x
    have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
    rw [hx]
    cases h0 : x 0 <;> cases h1 : x 1
    · exact hv.1.symm
    · exact hs.symm.trans hv.2.1.symm
    · exact hr.symm.trans hv.2.2.1.symm
    · exact hd.symm.trans hv.2.2.2.symm
  rw [he]
  exact affine_formula _ _ _

theorem full_affine_iff (f : Signature AlgebraicComplex 2) (hf : Full f) :
    Affine f ↔ CommonFourth f ∧ SignedCross f := by
  constructor
  · intro h
    exact ⟨fun x=>h.fourth_power_eq x ![false,false] (hf x) (hf ![false,false]),affine_signed_cross f hf h⟩
  · rintro ⟨hp,hc⟩
    have ha := hf ![false,false]
    have hr : (f ![true,false]/f ![false,false])^4=1 := by
      rw [div_pow,hp ![true,false],div_self (pow_ne_zero 4 ha)]
    have hs : (f ![false,true]/f ![false,false])^4=1 := by
      rw [div_pow,hp ![false,true],div_self (pow_ne_zero 4 ha)]
    obtain ⟨r,hr⟩ := fourthRootPhase_surjective_of_pow_four hr
    obtain ⟨s,hs⟩ := fourthRootPhase_surjective_of_pow_four hs
    have hr' : f ![false,false]*fourthRootPhase r=f ![true,false] := by rw [hr]; field_simp
    have hs' : f ![false,false]*fourthRootPhase s=f ![false,true] := by rw [hs]; field_simp
    rcases hc with hc|hc
    · exact affine_of_phases f ha r s false hr' hs' hc
    · exact affine_of_phases f ha r s true hr' hs' hc

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
end
