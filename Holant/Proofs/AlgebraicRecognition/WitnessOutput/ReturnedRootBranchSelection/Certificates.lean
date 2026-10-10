import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.Polynomial
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.Certified
import Mathlib.RingTheory.PrincipalIdealDomain


namespace Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
open Polynomial ComplexIsolation
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition

def inside (c : RootCode) (t : Certificate) : Bool :=
  decide (c.rectangle.reLower < t.center.1-t.radius ∧
    t.center.1+t.radius < c.rectangle.reUpper ∧
    c.rectangle.imLower < t.center.2-t.radius ∧
    t.center.2+t.radius < c.rectangle.imUpper)

theorem inside_sound {c : RootCode} {t : Certificate} (h : inside c t=true)
    {w : ℂ} (hw : t.rectangle.Contains w) : c.rectangle.Contains w := by
  simp only [inside,decide_eq_true_eq] at h
  simp only [Certificate.rectangle,RationalRectangle.Contains,Rat.cast_sub,Rat.cast_add] at hw
  have h₁ : (c.rectangle.reLower : ℝ)<(t.center.1 : ℝ)-(t.radius : ℝ) := by exact_mod_cast h.1
  have h₂ : (t.center.1 : ℝ)+(t.radius : ℝ)<(c.rectangle.reUpper : ℝ) := by exact_mod_cast h.2.1
  have h₃ : (c.rectangle.imLower : ℝ)<(t.center.2 : ℝ)-(t.radius : ℝ) := by exact_mod_cast h.2.2.1
  have h₄ : (t.center.2 : ℝ)+(t.radius : ℝ)<(c.rectangle.imUpper : ℝ) := by exact_mod_cast h.2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · exact h₁.trans hw.1
  · exact hw.2.1.trans h₂
  · exact h₃.trans hw.2.2.1
  · exact hw.2.2.2.trans h₄

/-- The existing arbitrary-small certificate producer is sufficient to keep
the same root embedding, even when the original relation has repeated roots. -/
theorem exists_divisor_certificate (c : RootCode) (z : ℂ) (hz : c.Represents z) :
    ∃ (g : Code.Poly) (t : Certificate), g.polynomial=minpoly ℚ z ∧
      t.check g=true ∧ inside c t=true := by
  let m : ℝ := min (z.re-(c.rectangle.reLower : ℝ))
    (min ((c.rectangle.reUpper : ℝ)-z.re)
      (min (z.im-(c.rectangle.imLower : ℝ)) ((c.rectangle.imUpper : ℝ)-z.im)))
  have hm : 0<m := by
    dsimp [m]
    exact lt_min (by linarith [hz.2.1.1])
      (lt_min (by linarith [hz.2.1.2.1])
        (lt_min (by linarith [hz.2.1.2.2.1]) (by linarith [hz.2.1.2.2.2])))
  let ε : ℝ := m/4
  have hε : 0<ε := by dsimp [ε]; positivity
  obtain ⟨g,t,hg,ht,hr,hs⟩ := exists_algebraic_certificate z
    (RootCode.represents_isAlgebraic hz) (show 0<ε/2 by positivity)
  have hrad : (t.radius : ℝ)<ε := by
    have hp := ((Certificate.check_iff g t).mp ht).1
    have hb := CommonPrimitive.radius_lt_of_rectangle_small t hp hs
    linarith
  have hm₁ : m ≤ z.re-(c.rectangle.reLower : ℝ) := min_le_left _ _
  have hm₂ : m ≤ (c.rectangle.reUpper : ℝ)-z.re :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hm₃ : m ≤ z.im-(c.rectangle.imLower : ℝ) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hm₄ : m ≤ (c.rectangle.imUpper : ℝ)-z.im :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbox : t.rectangle.Contains z := hr.2.1
  simp only [Certificate.rectangle,RationalRectangle.Contains,Rat.cast_sub,Rat.cast_add] at hbox
  refine ⟨g,t,hg,ht,?_⟩
  simp only [inside,decide_eq_true_eq]
  dsimp [ε] at hrad
  refine ⟨?_,?_,?_,?_⟩
  · have h : (c.rectangle.reLower : ℝ)<(t.center.1 : ℝ)-(t.radius : ℝ) := by
      linarith only [hm,hrad,hm₁,hbox.2.1]
    exact_mod_cast h
  · have h : (t.center.1 : ℝ)+(t.radius : ℝ)<(c.rectangle.reUpper : ℝ) := by
      linarith only [hm,hrad,hm₂,hbox.1]
    exact_mod_cast h
  · have h : (c.rectangle.imLower : ℝ)<(t.center.2 : ℝ)-(t.radius : ℝ) := by
      linarith only [hm,hrad,hm₃,hbox.2.2.2]
    exact_mod_cast h
  · have h : (t.center.2 : ℝ)+(t.radius : ℝ)<(c.rectangle.imUpper : ℝ) := by
      linarith only [hm,hrad,hm₄,hbox.2.2.1]
    exact_mod_cast h

structure Evidence where
  zero : Bool
  factor : Code.Poly
  relationQuotient : Code.Poly
  left : Code.Poly
  right : Code.Poly
  certificate : Certificate
  deriving DecidableEq, Encodable

def commonCheck (c : RootCode) (e : Evidence) : Bool :=
  e.certificate.check e.factor && inside c e.certificate &&
    Code.equal (Code.mul e.factor e.relationQuotient) c.coefficients

def valueCheck (q : Code.Poly) (e : Evidence) : Bool :=
  if e.zero then Code.equal (Code.mul e.factor e.left) q
  else Code.equal (Code.mul e.left e.factor ++ Code.mul e.right q) Code.one

def check (c : RootCode) (q : Code.Poly) (e : Evidence) : Bool :=
  commonCheck c e && valueCheck q e

/-- A successful factor certificate identifies exactly the root named by c;
it never chooses a different conjugate of the common factor. -/
theorem commonCheck_sound {c : RootCode} {z : ℂ} (hz : c.Represents z)
    {e : Evidence} (he : commonCheck c e=true) :
    Polynomial.aeval z e.factor.polynomial=0 := by
  simp only [commonCheck,Bool.and_eq_true] at he
  obtain ⟨w,hw⟩ := Certificate.check_sound he.1.1
  have hbox : c.rectangle.Contains w := inside_sound he.1.2 hw.2.1
  have hp : c.polynomial=e.factor.polynomial*e.relationQuotient.polynomial := by
    simpa only [RootCode.polynomial,Code.polynomial_mul] using
      ((Code.equal_iff _ _).mp he.2).symm
  have hfactor : Polynomial.aeval w e.factor.polynomial=0 := by
    simpa only [Certificate.rootCode,RootCode.polynomial] using hw.2.2.1
  have hroot : Polynomial.aeval w c.polynomial=0 := by
    rw [hp,map_mul,hfactor,zero_mul]
  have hsame : w=z := hz.2.2.2 w hbox hroot
  simpa only [hsame] using hfactor

theorem check_sound {c : RootCode} {z : ℂ} (hz : c.Represents z)
    {q : Code.Poly} {e : Evidence} (he : check c q e=true) :
    e.zero=true ↔ Polynomial.aeval z q.polynomial=0 := by
  simp only [check,Bool.and_eq_true] at he
  obtain ⟨hc,hv⟩ := he
  have hg := commonCheck_sound hz hc
  cases htag : e.zero with
  | true =>
    have hq : e.factor.polynomial*e.left.polynomial=q.polynomial := by
      have h := (Code.equal_iff (Code.mul e.factor e.left) q).mp
        (by simpa only [valueCheck,htag,ite_true] using hv)
      simpa only [Code.polynomial_mul] using h
    have hzero : Polynomial.aeval z q.polynomial=0 := by
      rw [←hq,map_mul,hg,zero_mul]
    simp [htag,hzero]
  | false =>
    have hbez : e.left.polynomial*e.factor.polynomial +
        e.right.polynomial*q.polynomial=1 := by
      have h := (Code.equal_iff (Code.mul e.left e.factor ++ Code.mul e.right q)
        Code.one).mp (by simpa only [valueCheck,htag,Bool.false_eq_true,ite_false] using hv)
      simpa only [RationalPolynomialCode.polynomial_append,Code.polynomial_mul,
        Code.polynomial_one] using h
    have hn : Polynomial.aeval z q.polynomial≠0 := by
      intro hq
      have hb := congrArg (Polynomial.aeval z) hbez
      simp only [map_add,map_mul,map_one,hg,hq,mul_zero,zero_add] at hb
      exact zero_ne_one hb
    simp [htag,hn]

theorem positive_complete {c : RootCode} {z : ℂ} (hz : c.Represents z)
    (q : Code.Poly) (hq : Polynomial.aeval z q.polynomial=0) :
    ∃ e : Evidence, e.zero=true ∧ check c q e=true := by
  obtain ⟨g,t,hg,ht,hi⟩ := exists_divisor_certificate c z hz
  obtain ⟨pquot,hpquot⟩ := minpoly.dvd_iff.mpr hz.2.2.1
  obtain ⟨qquot,hqquot⟩ := minpoly.dvd_iff.mpr hq
  obtain ⟨a,ha⟩ := RationalPolynomialCode.exists_code pquot
  obtain ⟨b,hb⟩ := RationalPolynomialCode.exists_code qquot
  let e : Evidence := ⟨true,g,a,b,[],t⟩
  refine ⟨e,rfl,?_⟩
  have hp : Code.equal (Code.mul g a) c.coefficients=true :=
    (Code.equal_iff _ _).mpr (by
      simpa only [Code.polynomial_mul,hg,ha,RootCode.polynomial] using hpquot.symm)
  have hq' : Code.equal (Code.mul g b) q=true :=
    (Code.equal_iff _ _).mpr (by simpa only [Code.polynomial_mul,hg,hb] using hqquot.symm)
  simp only [check,commonCheck,valueCheck,e,ht,hi,hp,hq',Bool.true_and,ite_true]

theorem negative_complete {c : RootCode} {z : ℂ} (hz : c.Represents z)
    (q : Code.Poly) (hq : Polynomial.aeval z q.polynomial≠0) :
    ∃ e : Evidence, e.zero=false ∧ check c q e=true := by
  obtain ⟨g,t,hg,ht,hi⟩ := exists_divisor_certificate c z hz
  obtain ⟨pquot,hpquot⟩ := minpoly.dvd_iff.mpr hz.2.2.1
  have hcop : IsCoprime (minpoly ℚ z) q.polynomial :=
    (minpoly.irreducible (RootCode.represents_isAlgebraic hz).isIntegral).coprime_iff_not_dvd.mpr
      (fun hd => hq (minpoly.dvd_iff.mp hd))
  obtain ⟨u,v,huv⟩ := hcop
  obtain ⟨a,ha⟩ := RationalPolynomialCode.exists_code pquot
  obtain ⟨b,hb⟩ := RationalPolynomialCode.exists_code u
  obtain ⟨d,hd⟩ := RationalPolynomialCode.exists_code v
  let e : Evidence := ⟨false,g,a,b,d,t⟩
  refine ⟨e,rfl,?_⟩
  have hp : Code.equal (Code.mul g a) c.coefficients=true :=
    (Code.equal_iff _ _).mpr (by
      simpa only [Code.polynomial_mul,hg,ha,RootCode.polynomial] using hpquot.symm)
  have hbz : Code.equal (Code.mul b g ++ Code.mul d q) Code.one=true :=
    (Code.equal_iff _ _).mpr (by
      simpa only [RationalPolynomialCode.polynomial_append,Code.polynomial_mul,
        Code.polynomial_one,hg,hb,hd] using huv)
  simp only [check,commonCheck,valueCheck,e,ht,hi,hp,hbz,Bool.true_and,
    Bool.false_eq_true,ite_false]

theorem check_complete {c : RootCode} {z : ℂ} (hz : c.Represents z) (q : Code.Poly) :
    ∃ e : Evidence, check c q e=true := by
  by_cases hq : Polynomial.aeval z q.polynomial=0
  · obtain ⟨e,_,he⟩ := positive_complete hz q hq
    exact ⟨e,he⟩
  · obtain ⟨e,_,he⟩ := negative_complete hz q hq
    exact ⟨e,he⟩

end Holant.LocalDrafts.EffectiveAlgebraic.WitnessOutput.ReturnedRootBranchSelection
