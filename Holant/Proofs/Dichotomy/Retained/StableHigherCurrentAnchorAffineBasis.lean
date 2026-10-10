import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorCriterion
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorLocalBasis
import Mathlib.Algebra.Polynomial.Roots

/-! Finite exact normalization of one affine basis shared by an entire ordinary
family. Literal pins restrict its inverse columns to six projective unary
lines. Literal Eq4 then restricts their relative scale by an explicitly indexed
fourth-root equation. The original common basis and its edge certificate are
retained throughout. No classification or finite-list assumption is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorAffineBasis
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option Elab.async false

abbrev pin := StableHigherCurrentAnchorLocalBasis.pin
abbrev eq4 := StableHigherCurrentAnchorCriterion.eq4

/-- The two pins and the four full-support affine unary directions. -/
abbrev LineCode := Bool ⊕ ZMod 4

def line : LineCode → Bool → AlgebraicComplex
  | .inl b, a => if a=b then 1 else 0
  | .inr q, a => if a then fourthRootPhase q else 1

/-- Every nonzero actual affine unary lies on one of the six explicit lines. -/
theorem unary_line (u : Signature AlgebraicComplex 1) (hu : Affine u)
    (hn : u ![false] ≠ 0 ∨ u ![true] ≠ 0) :
    ∃ c : AlgebraicComplex, c≠0 ∧ ∃ q : LineCode,
      ∀ a : Bool,u ![a]=c*line q a := by
  by_cases h0 : u ![false]=0
  · refine ⟨u ![true],hn.resolve_left (not_not_intro h0),.inl true,?_⟩
    intro a
    cases a <;> simp [line,h0]
  by_cases h1 : u ![true]=0
  · refine ⟨u ![false],h0,.inl false,?_⟩
    intro a
    cases a <;> simp [line,h1]
  have hp := hu.fourth_power_eq ![true] ![false] h1 h0
  have hr : (u ![true]/u ![false])^4=1 := by
    rw [div_pow,hp,div_self (pow_ne_zero 4 h0)]
  obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hr
  refine ⟨u ![false],h0,.inr q,?_⟩
  intro a
  cases a
  · simp [line]
  · simp only [line,ite_true]
    rw [hq]
    field_simp

/-- The inverse columns use independent projective line choices but only two
actual column scales; later the relative scale is constrained by Eq4. -/
theorem inverse_columns {H : SignatureFamily AlgebraicComplex} (B : InvertibleKernel)
    (h0 : (⟨1,pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,pin true⟩ : AnySignature AlgebraicComplex)∈H)
    (hB : IsCommonBasis affineClass H B) :
    ∃ c d : AlgebraicComplex,c≠0 ∧ d≠0 ∧ ∃ p q : LineCode,
      (∀ a,B.inverse a false=c*line p a) ∧
      (∀ a,B.inverse a true=d*line q a) := by
  have hd := determinant_ne_zero B.symm
  change determinant B.inverse≠0 at hd
  have n0 : B.inverse false false≠0 ∨ B.inverse true false≠0 := by
    by_contra h
    push Not at h
    exact hd (by simp [determinant,h.1,h.2])
  have n1 : B.inverse false true≠0 ∨ B.inverse true true≠0 := by
    by_contra h
    push Not at h
    exact hd (by simp [determinant,h.1,h.2])
  obtain ⟨c,hc,p,hp⟩ := unary_line (B.symm.action (pin false)) (hB.2 _ h0)
    (by simpa [StableHigherCurrentAnchorLocalBasis.pin_action,InvertibleKernel.symm] using n0)
  obtain ⟨d,hd,q,hq⟩ := unary_line (B.symm.action (pin true)) (hB.2 _ h1)
    (by simpa [StableHigherCurrentAnchorLocalBasis.pin_action,InvertibleKernel.symm] using n1)
  refine ⟨c,d,hc,hd,p,q,?_,?_⟩
  · simpa [StableHigherCurrentAnchorLocalBasis.pin_action,InvertibleKernel.symm] using hp
  · simpa [StableHigherCurrentAnchorLocalBasis.pin_action,InvertibleKernel.symm] using hq

/-- The fourth tensor power of one unary direction. -/
def fourthTensor (v : Bool → AlgebraicComplex) (x : Fin 4 → Bool) : AlgebraicComplex :=
  ∏i,v (x i)

@[simp] theorem fourthTensor_constant (v : Bool → AlgebraicComplex) (a : Bool) :
    fourthTensor v (fun _=>a)=v a^4 := by simp [fourthTensor]

theorem fourthTensor_one (v : Bool → AlgebraicComplex) :
    fourthTensor v ![true,false,false,false]=v true*v false^3 := by
  simp only [fourthTensor,Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero]
  ring

def probe : Fin 3 → Fin 4 → Bool :=
  ![fun _=>false,fun _=>true,![true,false,false,false]]

/-- Independent unary columns remain independent after taking their fourth
tensor powers. Two explicit Boolean words already witness independence. -/
theorem fourthTensor_independent (v w : Bool → AlgebraicComplex)
    (h : v false*w true-w false*v true≠0) :
    ∃ x y : Fin 3,
      fourthTensor v (probe x)*fourthTensor w (probe y)-
        fourthTensor w (probe x)*fourthTensor v (probe y)≠0 := by
  by_cases hv : v false=0
  · have hn : w false≠0 ∧ v true≠0 := by
      apply mul_ne_zero_iff.mp
      intro hz
      exact h (by simp [hv,hz])
    refine ⟨1,0,?_⟩
    simpa [probe,hv] using mul_ne_zero (pow_ne_zero 4 hn.2) (pow_ne_zero 4 hn.1)
  by_cases hw : w false=0
  · have hn : v false≠0 ∧ w true≠0 := by
      apply mul_ne_zero_iff.mp
      simpa [hw] using h
    refine ⟨0,1,?_⟩
    simpa [probe,hw] using mul_ne_zero (pow_ne_zero 4 hn.1) (pow_ne_zero 4 hn.2)
  refine ⟨0,2,?_⟩
  change fourthTensor v (fun _=>false)*fourthTensor w ![true,false,false,false]-
    fourthTensor w (fun _=>false)*fourthTensor v ![true,false,false,false]≠0
  rw [fourthTensor_constant,fourthTensor_constant,fourthTensor_one,fourthTensor_one]
  have he : v false^4*(w true*w false^3)-w false^4*(v true*v false^3)=
      v false^3*w false^3*(v false*w true-w false*v true) := by ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hv) (pow_ne_zero 3 hw)) h

abbrev PhaseCode := Option (ZMod 4)
def phase : PhaseCode → AlgebraicComplex
  | none => 0
  | some q => fourthRootPhase q

/-- Every value relative to a supported affine value is zero or a fourth root. -/
theorem affine_ratio {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Affine f)
    (x y : Fin n → Bool) (hx : f x≠0) : ∃q : PhaseCode,f y=phase q*f x := by
  by_cases hy : f y=0
  · exact ⟨none,by simp [phase,hy]⟩
  have hp : (f y/f x)^4=1 := by
    rw [div_pow,hf.fourth_power_eq y x hy hx,div_self (pow_ne_zero 4 hx)]
  obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hp
  refine ⟨some q,?_⟩
  rw [phase,hq,div_mul_cancel₀ _ hx]

/-- The exact finite fourth-power constraint. Independence selects one
supported reference value; its affine ratio determines the relative scale. -/
theorem relative_scale_constraint (v w : Bool → AlgebraicComplex)
    (c d : AlgebraicComplex) (hc : c≠0)
    (hi : v false*w true-w false*v true≠0)
    (hf : Affine (fun x=>c^4*fourthTensor v x+d^4*fourthTensor w x)) :
    ∃ x y : Fin 3,∃q : PhaseCode,
      fourthTensor w (probe y)-phase q*fourthTensor w (probe x)≠0 ∧
      (d/c)^4=(phase q*fourthTensor v (probe x)-fourthTensor v (probe y))/
        (fourthTensor w (probe y)-phase q*fourthTensor w (probe x)) := by
  let f : Signature AlgebraicComplex 4 := fun x=>c^4*fourthTensor v x+d^4*fourthTensor w x
  obtain ⟨x,y,hxy⟩ := fourthTensor_independent v w hi
  have selected : ∃ x y : Fin 3,f (probe x)≠0 ∧
      fourthTensor v (probe x)*fourthTensor w (probe y)-fourthTensor w (probe x)*fourthTensor v (probe y)≠0 := by
    by_cases hx : f (probe x)=0
    · refine ⟨y,x,?_,?_⟩
      · intro hy
        have hz : c^4*(fourthTensor v (probe x)*fourthTensor w (probe y)-
            fourthTensor w (probe x)*fourthTensor v (probe y))=0 := by
          dsimp [f] at hx hy
          linear_combination fourthTensor w (probe y)*hx-fourthTensor w (probe x)*hy
        exact mul_ne_zero (pow_ne_zero 4 hc) hxy hz
      · intro he
        apply hxy
        linear_combination -he
    · exact ⟨x,y,hx,hxy⟩
  obtain ⟨x,y,hx,hxy⟩ := selected
  obtain ⟨q,hq⟩ := affine_ratio hf (probe x) (probe y) hx
  have hp : d^4*(fourthTensor w (probe y)-phase q*fourthTensor w (probe x))=
      c^4*(phase q*fourthTensor v (probe x)-fourthTensor v (probe y)) := by
    linear_combination hq
  have hd : fourthTensor w (probe y)-phase q*fourthTensor w (probe x)≠0 := by
    intro hd
    have hv : phase q*fourthTensor v (probe x)-fourthTensor v (probe y)=0 := by
      apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 4 hc)
      rw [←hp,hd,mul_zero]
    apply hxy
    linear_combination fourthTensor v (probe x)*hd+fourthTensor w (probe x)*hv
  refine ⟨x,y,q,hd,?_⟩
  rw [div_pow]
  apply (div_eq_div_iff (pow_ne_zero 4 hc) hd).mpr
  linear_combination hp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorAffineBasis
end
