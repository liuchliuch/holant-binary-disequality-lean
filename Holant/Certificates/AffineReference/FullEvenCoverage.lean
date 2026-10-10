import Holant.Certificates.AffineReference.FullEvenData
import Holant.Tractable.TwoTranslate.Phase

/-! Semantic coverage of all normalized full-even affine signatures by the
finite 512-parameter table. The finite family is derived from an actual Affine
witness, rather than assumed as an input list. -/
namespace Holant.Certificates.AffineReference
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def evenChart (y : Fin 3 → Bool) : Fin 4 → Bool := ![y 0,y 1,y 2,y 0 ^^ y 1 ^^ y 2]

 theorem evenChart_affine : TwoTranslate.IsAffineMap evenChart := by
  unfold TwoTranslate.IsAffineMap
  decide

 theorem evenChart_even : ∀ y : Fin 3 → Bool,evenWord (evenChart y)=true := by decide

 theorem evenChart_original : ∀ x : Fin 4 → Bool,evenWord x=true →
    evenChart ![x 0,x 1,x 2]=x := by decide

 def phaseCode (p : Fin 4) : ZMod 4 := p.val
 def phaseOfCode (z : ZMod 4) : Fin 4 := ⟨z.val,z.val_lt⟩

 @[simp] theorem phaseCode_phaseOfCode (z : ZMod 4) : phaseCode (phaseOfCode z)=z := by
  simp [phaseCode,phaseOfCode]

 theorem phaseCode_add (a b : Fin 4) : phaseCode (a+b)=phaseCode a+phaseCode b := by
  revert a b; decide
 theorem phaseCode_mul (a b : Fin 4) : phaseCode (a*b)=phaseCode a*phaseCode b := by
  revert a b; decide
 @[simp] theorem phaseCode_bit (b : Bool) : phaseCode (phaseBit b)=bitValue (ZMod 4) b := by cases b <;> rfl
 @[simp] theorem phaseCode_sign (b : Bool) : phaseCode (signPhase b)=if b then 2 else 0 := by cases b <;> rfl

 def evenAlg (p : EvenParameters) : Signature AlgebraicComplex 4 := fun x =>
  if evenWord x then fourthRootPhase (phaseCode (evenPhase p x)) else 0

 def parametersOfPhase (Q : QuadraticPhase 3) : EvenParameters :=
  ((phaseOfCode (Q.linear 0),phaseOfCode (Q.linear 1),phaseOfCode (Q.linear 2)),
    decide (Q.mixed 0 1=2),decide (Q.mixed 0 2=2),decide (Q.mixed 1 2=2))

 theorem mixed_code (Q : QuadraticPhase 3) (i j : Fin 3) (hij : i<j) :
    (if decide (Q.mixed i j=2) then (2 : ZMod 4) else 0)=Q.mixed i j := by
  have hn : (0 : ZMod 4)≠2 := by decide
  rcases Q.even_mixed i j hij with h | h <;> simp [h,hn]

 theorem parametersOfPhase_eval (Q : QuadraticPhase 3) (y : Fin 3 → Bool) :
    phaseCode (evenPhase (parametersOfPhase Q) (evenChart y))=Q.eval y-Q.constant := by
  simp only [evenPhase,phaseCode_add,phaseCode_mul,phaseCode_bit,phaseCode_sign,
    parametersOfPhase,phaseCode_phaseOfCode]
  rw [mixed_code Q 0 1 (by decide),mixed_code Q 0 2 (by decide),mixed_code Q 1 2 (by decide)]
  simp [QuadraticPhase.eval,evenChart,Fin.sum_univ_succ]
  ring

 theorem affine_even_chart (h : Signature AlgebraicComplex 4) (ha : Affine h)
    (hs : ∀ x,h x≠0 ↔ evenWord x=true) : Affine (fun y => h (evenChart y)) := by
  rcases ha with hz | ⟨c,hc,S,Q,hf⟩
  · have hn := (hs (evenChart (fun _ => false))).mpr (evenChart_even _)
    simp [hz] at hn
  have hholds (y : Fin 3 → Bool) : S.Holds (evenChart y) := by
    have hn := (hs (evenChart y)).mpr (evenChart_even y)
    rw [hf] at hn
    by_contra hh
    simp [affineFormula,hh] at hn
  have H := (TwoTranslate.affine_quadratic_precompose Q evenChart evenChart_affine).scale c
  convert H using 1
  funext y
  rw [hf]
  simp [affineFormula,hholds y]

 theorem full_even_coverage (h : Signature AlgebraicComplex 4) (ha : Affine h)
    (hs : ∀ x,h x≠0 ↔ evenWord x=true) (h0 : h (fun _ => false)=1) :
    ∃ p : EvenParameters,h=evenAlg p := by
  have hc := affine_even_chart h ha hs
  have hn (y : Fin 3 → Bool) : h (evenChart y)≠0 := (hs _).mpr (evenChart_even y)
  rcases hc with hz | ⟨c,hc,S,Q,hformula⟩
  · exact False.elim (hn (fun _ => false) (congrFun hz _))
  have hholds (y : Fin 3 → Bool) : S.Holds y := by
    have hne := hn y
    rw [congrFun hformula y] at hne
    by_contra hh
    simp [affineFormula,hh] at hne
  have hscale : c*fourthRootPhase Q.constant=1 := by
    have H := congrFun hformula (fun _ => false)
    have he : evenChart (fun _ => false)=(fun _ => false) := by decide
    change h (evenChart (fun _ => false))=affineFormula c S Q (fun _ => false) at H
    rw [he,h0] at H
    simpa [affineFormula,hholds,QuadraticPhase.eval] using H.symm
  have hvalues (y : Fin 3 → Bool) : h (evenChart y)=fourthRootPhase (Q.eval y-Q.constant) := by
    rw [congrFun hformula y]
    simp only [affineFormula,if_pos (hholds y),fourthRootPhase_sub]
    have hcval : c=1/fourthRootPhase Q.constant :=
      (eq_div_iff (fourthRootPhase_ne_zero Q.constant)).mpr hscale
    rw [hcval]
    ring
  refine ⟨parametersOfPhase Q,?_⟩
  funext x
  by_cases hx : evenWord x=true
  · have he := evenChart_original x hx
    rw [←he,hvalues]
    simp only [evenAlg,evenChart_even,ite_true,parametersOfPhase_eval]
  · have hz : h x=0 := by by_contra hn';exact hx ((hs x).mp hn')
    simp [evenAlg,hx,hz]

end
end Holant.Certificates.AffineReference
