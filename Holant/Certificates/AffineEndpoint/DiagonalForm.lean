import Holant.Certificates.AffineEndpoint.CoreSource
import Holant.EightVertex.ProductAnchor.GeneralizedEquality
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Exact algebraic diagonal reconstruction from checked endpoint/central
coefficient identities. This supplies the semantic bridge for A.4 certificates. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable
open Holant.EightVertex.ProductAnchor
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def zeroWord : Fin 4→Bool := fun _ => false
 def oneWord : Fin 4→Bool := fun _ => true
 def centralWord : Fin 6→(Fin 4→Bool) :=
  ![![false,false,true,true],![false,true,false,true],![false,true,true,false],
    ![true,false,false,true],![true,false,true,false],![true,true,false,false]]

 theorem centralWord_weight : ∀i,Holant.weight (centralWord i)=2 := by decide +kernel
 theorem zeroWord_weight : Holant.weight zeroWord=0 := by decide +kernel
 theorem oneWord_weight : Holant.weight oneWord=4 := by decide +kernel
 theorem word_layer_cases : ∀x : Fin 4→Bool,
    Holant.weight x%2=1 ∨ x=zeroWord ∨ x=oneWord ∨ ∃i,x=centralWord i := by decide +kernel

 def diagonalAction (t : AlgebraicComplex) (h : Signature AlgebraicComplex 4) :
    Signature AlgebraicComplex 4 := Signature.coordinateAction (fun _ => diagonalKernel 1 t) h

 theorem diagonalAction_apply (t : AlgebraicComplex) (h : Signature AlgebraicComplex 4) (x : Fin 4→Bool) :
    diagonalAction t h x=t^(Holant.weight x)*h x := by
  rw [diagonalAction,coordinateAction_diagonal]
  simp [diagonalCoefficient_eq_weight]

 theorem algebraic_root (a : AlgebraicComplex) (ha : a≠0) (n : ℕ) (hn : 0<n) :
    ∃t : AlgebraicComplex,t≠0 ∧ t^n=a := by
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ) hn
  let u : AlgebraicComplex := ⟨t,IsIntegral.of_pow (n := n) hn (by rw [ht]; exact a.property)⟩
  have hu : u^n=a := Subtype.ext ht
  refine ⟨u,?_,hu⟩
  intro hz
  exact ha (by simpa [hz,hn.ne'] using hu.symm)

/-- The finite checker supplies literal equalities, after which an actual
algebraic square root gives the required uniform four-port action. -/
 theorem diagonal_form_of_layers (g h : Signature AlgebraicComplex 4)
    (hg : ∀x,Holant.weight x%2=1→g x=0) (hh : ∀x,Holant.weight x%2=1→h x=0)
    (gamma lam : AlgebraicComplex) (hgamma : gamma≠0) (hlam : lam≠0)
    (hzero : g zeroWord=gamma*h zeroWord)
    (hone : g oneWord=gamma*lam^2*h oneWord)
    (hcentral : ∀i,g (centralWord i)=gamma*lam*h (centralWord i)) :
    ∃t : AlgebraicComplex,t≠0 ∧ g=gamma • diagonalAction t h := by
  obtain ⟨t,ht,htsq⟩ := algebraic_root lam hlam 2 (by decide)
  refine ⟨t,ht,?_⟩
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,diagonalAction_apply]
  rcases word_layer_cases x with ho|rfl|rfl|⟨i,rfl⟩
  · rw [hg x ho,hh x ho,mul_zero,mul_zero]
  · simpa [zeroWord_weight] using hzero
  · rw [oneWord_weight,show t^4=lam^2 from by rw [show 4=2*2 from rfl,pow_mul,htsq]]
    simpa [mul_assoc] using hone
  · rw [centralWord_weight,htsq]
    simpa [mul_assoc] using hcentral i

/-- The zero-central-layer case uses a genuine algebraic fourth root. -/
 theorem diagonal_form_of_endpoints (g h : Signature AlgebraicComplex 4)
    (hg : EndpointEven g) (hh : EndpointEven h)
    (hgc : ∀i,g (centralWord i)=0) (hhc : ∀i,h (centralWord i)=0) :
    ∃gamma t : AlgebraicComplex,gamma≠0 ∧ t≠0 ∧ g=gamma • diagonalAction t h := by
  let gamma := g zeroWord/h zeroWord
  have hg0 : g zeroWord≠0 := hg.1
  have hh0 : h zeroWord≠0 := hh.1
  have hg1 : g oneWord≠0 := hg.2.1
  have hh1 : h oneWord≠0 := hh.2.1
  have hc : gamma≠0 := div_ne_zero hg0 hh0
  obtain ⟨t,ht,hpow⟩ := algebraic_root (g oneWord/(gamma*h oneWord))
    (div_ne_zero hg1 (mul_ne_zero hc hh1)) 4 (by decide)
  refine ⟨gamma,t,hc,ht,?_⟩
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,diagonalAction_apply]
  rcases word_layer_cases x with ho|rfl|rfl|⟨i,rfl⟩
  · rw [hg.2.2 x ho,hh.2.2 x ho,mul_zero,mul_zero]
  · rw [zeroWord_weight,pow_zero,one_mul]
    exact (div_mul_cancel₀ _ hh0).symm
  · rw [oneWord_weight,hpow]
    field_simp
  · rw [hgc i,hhc i,mul_zero,mul_zero]

end
end Holant.Certificates.AffineEndpoint
