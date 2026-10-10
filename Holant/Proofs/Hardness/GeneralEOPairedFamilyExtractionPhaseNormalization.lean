import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseMinor

/-! Removing the actual unary and pair phases by positive powers. Every
normalizing factor will be expressed as literal coordinate restrictions; no
phase-recognition oracle or Möbius coefficients are supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization
open Holant Holant.Tractable
open scoped BigOperators
namespace A
export AffinePhase (word basis origin)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {n : ℕ}
abbrev Edge (n : ℕ) := {e : Fin n×Fin n // e.1<e.2}

variable (g : Signature AlgebraicComplex n)

def unary (i : Fin n) (x : Fin n → Bool) : AlgebraicComplex :=
  if x i then g (A.basis i) else 1

def pairTable (e : Edge n) : Signature AlgebraicComplex 2 := fun z =>
  if z 0 then (if z 1 then g (A.word {e.val.1,e.val.2}) else g (A.basis e.val.1))
  else (if z 1 then g (A.basis e.val.2) else 1)

def interaction (e : Edge n) : AlgebraicComplex :=
  g (A.word {e.val.1,e.val.2})*g (A.basis e.val.1)^3*g (A.basis e.val.2)^3

def pair (e : Edge n) (x : Fin n → Bool) : AlgebraicComplex :=
  if x e.val.1 && x e.val.2 then interaction g e else 1

def correction (x : Fin n → Bool) : AlgebraicComplex :=
  (∏i,unary g i x^3)*(∏e : Edge n,pair g e x^3)

def residual : Signature AlgebraicComplex n := fun x => g x*correction g x

variable (hfour : ∀x,g x^4=1)

include hfour in
theorem unary_four (i : Fin n) (x : Fin n → Bool) : unary g i x^4=1 := by
  cases h : x i <;> simp [unary,h,hfour]

include hfour in
theorem interaction_four (e : Edge n) : interaction g e^4=1 := by
  simp only [interaction,mul_pow]
  rw [pow_right_comm (g (A.basis e.val.1)) 3 4,pow_right_comm (g (A.basis e.val.2)) 3 4]
  rw [hfour,hfour,hfour]
  norm_num

include hfour in
theorem pair_four (e : Edge n) (x : Fin n → Bool) : pair g e x^4=1 := by
  unfold pair
  split_ifs
  · exact interaction_four g hfour e
  · norm_num

include hfour in
theorem correction_four (x : Fin n → Bool) : correction g x^4=1 := by
  unfold correction
  rw [mul_pow,←Finset.prod_pow,←Finset.prod_pow]
  have hu : ∀i : Fin n,(unary g i x^3)^4=1 := by
    intro i
    rw [pow_right_comm,unary_four g hfour,one_pow]
  have he : ∀e : Edge n,(pair g e x^3)^4=1 := by
    intro e
    rw [pow_right_comm,pair_four g hfour,one_pow]
  simp only [hu,he,Finset.prod_const_one,one_mul]

include hfour in
theorem residual_four (x : Fin n → Bool) : residual g x^4=1 := by
  rw [residual,mul_pow,hfour,correction_four g hfour,one_mul]

include hfour in
theorem pair_formula (e : Edge n) (x : Fin n → Bool) :
    pair g e x=pairTable g e ![x e.val.1,x e.val.2]*
      unary g e.val.1 x^3*unary g e.val.2 x^3 := by
  have ha := hfour (A.basis e.val.1)
  have hb := hfour (A.basis e.val.2)
  cases h0 : x e.val.1 <;> cases h1 : x e.val.2
  · simp [pair,pairTable,unary,h0,h1]
  · simpa [pair,pairTable,unary,h0,h1,←pow_succ'] using hb.symm
  · simpa [pair,pairTable,unary,h0,h1,←pow_succ'] using ha.symm
  · simp [pair,pairTable,unary,interaction,h0,h1]

include hfour in
theorem unary_affine (i : Fin n) : Affine (unary g i) := by
  obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four (hfour (A.basis i))
  let Q : QuadraticPhase n := ⟨0,fun j => if j=i then q else 0,fun _ _=>0,fun _ _ _=>Or.inl rfl⟩
  convert affine_formula 1 (AffineSystem.unconstrained n) Q using 1
  funext x
  simp only [affineFormula,AffineSystem.unconstrained_holds,ite_true,one_mul,
    QuadraticPhase.eval,Q,zero_add,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    ]
  cases h : x i <;> simp [unary,bitValue,h,hq]

theorem affine_pow {f : Signature AlgebraicComplex n} (h : Affine f) (k : ℕ) :
    Affine (fun x => f x^k) := by
  induction k with
  | zero => simpa only [pow_zero] using affine_constant n 1
  | succ k ih => simpa only [pow_succ] using ih.mul h

theorem affine_prod {ι : Type*} [Fintype ι] (fs : ι → Signature AlgebraicComplex n)
    (h : ∀i,Affine (fs i)) : Affine (fun x => ∏i,fs i x) := by
  have hh (s : Finset ι) : Affine (fun x => ∏i∈s,fs i x) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty] using affine_constant n 1
    | insert i s hi ih => simpa only [Finset.prod_insert hi] using (h i).mul ih
  exact hh Finset.univ

include hfour in
theorem pair_affine (hpair : ∀e : Edge n,Affine (pairTable g e)) (e : Edge n) : Affine (pair g e) := by
  have hm : TwoTranslate.IsAffineMap (fun x : Fin n → Bool => ![x e.val.1,x e.val.2]) := by
    convert coordinates_isAffineMap (![e.val.1,e.val.2] : Fin 2 → Fin n) using 1
    funext x j
    fin_cases j <;> rfl
  have hp := (hpair e).precompose (fun x : Fin n → Bool => ![x e.val.1,x e.val.2]) hm
  have hh := (hp.mul (affine_pow (unary_affine g hfour e.val.1) 3)).mul
    (affine_pow (unary_affine g hfour e.val.2) 3)
  convert hh using 1
  funext x
  exact pair_formula g hfour e x

include hfour in
theorem correction_affine (hpair : ∀e : Edge n,Affine (pairTable g e)) : Affine (correction g) :=
  (affine_prod (fun i => fun x => unary g i x^3) (fun i=>affine_pow (unary_affine g hfour i) 3)).mul
    (affine_prod (fun e => fun x => pair g e x^3) (fun e=>affine_pow (pair_affine g hfour hpair e) 3))

include hfour in
theorem residual_nonconstant (ha : ¬Affine g) (hpair : ∀e : Edge n,Affine (pairTable g e)) :
    ∃x,residual g x≠1 := by
  by_contra hn
  have hh : ∀x,residual g x=1 := by simpa only [not_exists,not_not] using hn
  have he : g=(fun x => correction g x^3) := by
    funext x
    have hc := correction_four g hfour x
    have hr := hh x
    change g x*correction g x=1 at hr
    calc
      g x=g x*correction g x^4 := by rw [hc,mul_one]
      _=(g x*correction g x)*correction g x^3 := by ring
      _=correction g x^3 := by rw [hr,one_mul]
  apply ha
  rw [he]
  exact affine_pow (correction_affine g hfour hpair) 3

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization
