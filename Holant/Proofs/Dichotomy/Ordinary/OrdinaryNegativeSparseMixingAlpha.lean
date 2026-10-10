import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMixingX
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeOcticCommonBasis
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicCriterion
import Holant.Proofs.Hardness.EOBinaryPlaneClassification

/-! The rank-one, rank-two/three-bundle, and rank-three/seven-bundle octic
resources are really non-affine. This is proved from their exact coefficients
and affine phase cores, not supplied as a classification assumption. Literal
X conversion therefore gives actual doubled non-affine resources at all three
small complete-support ranks, retaining arbitrary original nonzero scales. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingAlpha
open Holant Holant.Tractable
open scoped BigOperators
namespace N
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization (affine_pow)
end N
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification (affine_signed_cross)
end B
namespace X
export OrdinaryNegativeSparseMixingX (trace not_affine trace_value)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

def codeThree (x : Fin 2→Bool) : Fin 3→Bool := ![x 0,x 1,x 0^^x 1]
def codeSeven (x : Fin 3→Bool) : Fin 7→Bool :=
  ![x 0,x 1,x 2,x 1^^x 2,x 0^^x 2,x 0^^x 1,(x 0^^x 1)^^x 2]

def twist {n : ℕ} (x : Fin n→Bool) : AlgebraicComplex := ∏i,if x i then zetaEight else 1

def phaseOne : Signature AlgebraicComplex 1 := twist
def phaseThree : Signature AlgebraicComplex 2 := fun x=>twist (codeThree x)
def phaseSeven : Signature AlgebraicComplex 3 := fun x=>twist (codeSeven x)

theorem twist_nonzero {n : ℕ} (x : Fin n→Bool) : twist x≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases x i <;> simp [zetaEight_ne_zero]

theorem phaseThree_formula (x : Fin 2→Bool) :
    phaseThree x=if x 0 || x 1 then imaginaryUnit else 1 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [phaseThree,twist,codeThree,Fin.prod_univ_three,h0,h1,←pow_two,zetaEight_sq]

theorem phaseSeven_formula (x : Fin 3→Bool) :
    phaseSeven x=if x 0 || x 1 || x 2 then -1 else 1 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [phaseSeven,twist,codeSeven,Fin.prod_univ_succ,h0,h1,h2]
  all_goals convert zetaEight_pow_four using 1 <;> ring

theorem phaseOne_not_affine : ¬Affine phaseOne := by
  intro h
  have he := h.fourth_power_eq (fun _=>false) (fun _=>true)
    (twist_nonzero _) (twist_nonzero _)
  norm_num [phaseOne,twist,zetaEight_pow_four] at he

theorem phaseThree_not_affine : ¬Affine phaseThree := by
  intro h
  have hs := B.affine_signed_cross phaseThree (fun x=>twist_nonzero _) h
  have hsq : (phaseThree ![false,false]*phaseThree ![true,true])^2=
      (phaseThree ![false,true]*phaseThree ![true,false])^2 := by
    rcases hs with hs|hs
    · rw [hs]
    · rw [hs,neg_sq]
  norm_num [phaseThree_formula,←pow_two,imaginaryUnit_sq] at hsq

theorem phaseSeven_not_affine : ¬Affine phaseSeven := by
  intro h
  have hfull (x : Fin 3→Bool) : phaseSeven x≠0 := twist_nonzero (codeSeven x)
  have ht := AffinePhase.thirdTrivial_of_affine hfull h
    (fun _=>false) ![true,false,false] ![false,true,false] ![false,false,true]
  norm_num [AffinePhase.thirdRatio,AffinePhase.xor,phaseSeven_formula] at ht

/-- An arbitrary full-support affine core cannot cancel the non-affine
phase. Its complete original coefficient is removed algebraically using its
third positive power and the common fourth power, never as a free gadget. -/
theorem multiply_affine_core {n : ℕ} (f p : Signature AlgebraicComplex n)
    (hf : ¬Affine f) (hp : Affine p) (full : ∀x,p x≠0) :
    ¬Affine (fun x=>f x*p x) := by
  intro h
  apply hf
  have hA := (h.mul (N.affine_pow hp 3)).scale ((p (AffinePhase.origin n)^4)⁻¹)
  convert hA using 1
  funext x
  have he := hp.fourth_power_eq x (AffinePhase.origin n) (full x) (full _)
  calc
    f x=(p (AffinePhase.origin n)^4)⁻¹*(f x*p x^4) := by
      rw [he,mul_comm (f x),←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ (full _)),one_mul]
    _=(p (AffinePhase.origin n)^4)⁻¹*(f x*p x*p x^3) := by ring

theorem codeThree_affine : TwoTranslate.IsAffineMap codeThree := by unfold TwoTranslate.IsAffineMap; decide
theorem codeSeven_affine : TwoTranslate.IsAffineMap codeSeven := by unfold TwoTranslate.IsAffineMap; decide

def essentialThree (p : Signature AlgebraicComplex 2) : Signature AlgebraicComplex 3 :=
  fun x=>if x 2=(x 0^^x 1) then twist x*p ![x 0,x 1] else 0

def essentialSeven (p : Signature AlgebraicComplex 3) : Signature AlgebraicComplex 7 :=
  fun x=>if x=codeSeven ![x 0,x 1,x 2] then twist x*p ![x 0,x 1,x 2] else 0

theorem essentialThree_restrict (p : Signature AlgebraicComplex 2) (x : Fin 2→Bool) :
    essentialThree p (codeThree x)=phaseThree x*p x := by
  have hx : (![x 0,x 1] : Fin 2→Bool)=x := by funext i; fin_cases i <;> rfl
  change (if (x 0^^x 1)=(x 0^^x 1) then twist (codeThree x)*p ![x 0,x 1] else 0)=_
  rw [if_pos rfl,hx]
  rfl

theorem essentialSeven_restrict (p : Signature AlgebraicComplex 3) (x : Fin 3→Bool) :
    essentialSeven p (codeSeven x)=phaseSeven x*p x := by
  have hx : (![x 0,x 1,x 2] : Fin 3→Bool)=x := by funext i; fin_cases i <;> rfl
  change (if codeSeven x=codeSeven ![x 0,x 1,x 2] then twist (codeSeven x)*p ![x 0,x 1,x 2] else 0)=_
  rw [hx,if_pos rfl]
  rfl

theorem essentialThree_not_affine (p : Signature AlgebraicComplex 2)
    (hp : Affine p) (full : ∀x,p x≠0) : ¬Affine (essentialThree p) := by
  intro h
  have hh := h.precompose codeThree codeThree_affine
  apply multiply_affine_core phaseThree p phaseThree_not_affine hp full
  simpa only [essentialThree_restrict] using hh

theorem essentialSeven_not_affine (p : Signature AlgebraicComplex 3)
    (hp : Affine p) (full : ∀x,p x≠0) : ¬Affine (essentialSeven p) := by
  intro h
  have hh := h.precompose codeSeven codeSeven_affine
  apply multiply_affine_core phaseSeven p phaseSeven_not_affine hp full
  simpa only [essentialSeven_restrict] using hh

theorem one_X_not_affine (p : Signature AlgebraicComplex 1)
    (hp : Affine p) (full : ∀x,p x≠0) (d : AlgebraicComplex) (hd : d≠0) :
    ¬Affine (X.trace (fun x=>phaseOne x*p x) d) :=
  X.not_affine _ d hd (multiply_affine_core phaseOne p phaseOne_not_affine hp full)

theorem three_X_not_affine (p : Signature AlgebraicComplex 2)
    (hp : Affine p) (full : ∀x,p x≠0) (d : AlgebraicComplex) (hd : d≠0) :
    ¬Affine (X.trace (essentialThree p) d) :=
  X.not_affine _ d hd (essentialThree_not_affine p hp full)

theorem seven_X_not_affine (p : Signature AlgebraicComplex 3)
    (hp : Affine p) (full : ∀x,p x≠0) (d : AlgebraicComplex) (hd : d≠0) :
    ¬Affine (X.trace (essentialSeven p) d) :=
  X.not_affine _ d hd (essentialSeven_not_affine p hp full)


/-- A coefficient-level version independent of the presentation of the
original affine core. It covers the actual inverse-action definition of the
common alpha class, without choosing a convention for alpha versus its inverse. -/
theorem not_affine_on_code {m n : ℕ} (f : Signature AlgebraicComplex n)
    (code : (Fin m→Bool)→(Fin n→Bool)) (linear : TwoTranslate.IsAffineMap code)
    (phase_bad : ¬Affine (fun x=>twist (code x)))
    (twisted : Affine (fun x=>twist x*f x)) (full : ∀x,f (code x)≠0) : ¬Affine f := by
  intro hf
  exact multiply_affine_core (fun x=>twist (code x)) (fun x=>f (code x))
    phase_bad (hf.precompose code linear) full (twisted.precompose code linear)

theorem twist_action {n : ℕ} (f : Signature AlgebraicComplex n) :
    (OrdinaryNegativeOcticCommonBasis.basis true).symm.action f=(fun x=>twist x*f x) := by
  rw [OrdinaryNegativeOcticCommonBasis.action]
  rfl

theorem three_not_affine_of_alpha (f : Signature AlgebraicComplex 3)
    (ha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (full : ∀x : Fin 2→Bool,f (codeThree x)≠0) : ¬Affine f := by
  rw [twist_action] at ha
  exact not_affine_on_code f codeThree codeThree_affine phaseThree_not_affine ha full

theorem seven_not_affine_of_alpha (f : Signature AlgebraicComplex 7)
    (ha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (full : ∀x : Fin 3→Bool,f (codeSeven x)≠0) : ¬Affine f := by
  rw [twist_action] at ha
  exact not_affine_on_code f codeSeven codeSeven_affine phaseSeven_not_affine ha full

theorem three_X_not_affine_of_alpha (f : Signature AlgebraicComplex 3)
    (ha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (full : ∀x : Fin 2→Bool,f (codeThree x)≠0) (d : AlgebraicComplex) (hd : d≠0) :
    ¬Affine (X.trace f d) := X.not_affine f d hd (three_not_affine_of_alpha f ha full)

theorem seven_X_not_affine_of_alpha (f : Signature AlgebraicComplex 7)
    (ha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
    (full : ∀x : Fin 3→Bool,f (codeSeven x)≠0) (d : AlgebraicComplex) (hd : d≠0) :
    ¬Affine (X.trace f d) := X.not_affine f d hd (seven_not_affine_of_alpha f ha full)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseMixingAlpha
end
