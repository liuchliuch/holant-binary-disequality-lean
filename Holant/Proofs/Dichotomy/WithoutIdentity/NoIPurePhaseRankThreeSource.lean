import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankThreeCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRoot
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRecipeFactor
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidenceCore

/-! A root-sixteen weight phase cancels the genuine minimal cubic sign when
all seven signed original character incidences are two modulo four. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankThreeSource
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankDescent
open scoped BigOperators
namespace R
export NoIPurePhaseRankTwoScalar (rho rho_nonzero rho_four rho_eight rho_sixteen)
end R
namespace C
export NoIPurePhaseIncidenceCore.C (codeSeven)
end C
namespace P
export NoIPurePhaseRecipeFactor (Port word incidence)
end P
namespace A
export NoIPurePhaseRankThreeCore (phaseSeven phaseSeven_square phaseSeven_affine)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option Elab.async false
variable {n : ℕ}

theorem codeSeven_affine : TwoTranslate.IsAffineMap C.codeSeven := by
  unfold TwoTranslate.IsAffineMap
  decide

def twist (a : AlgebraicComplex) (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex n:=
  fun x=>a^(weight x)*f x

theorem rho_zpow_mod (d : ℤ) : R.rho^d=R.rho^(d%16) := by
  calc
    R.rho^d=R.rho^(d%16+16*(d/16)):=by congr 1;omega
    _=R.rho^(d%16)*(R.rho^(16 : ℤ))^(d/16):=by
      rw [zpow_add₀ R.rho_nonzero,zpow_mul]
    _=R.rho^(d%16):=by simp [R.rho_sixteen]

theorem signed_two_fourth (d : ℤ) (residue : d%4=2) : (R.rho^d)^4= -1 := by
  have he:4*d%16=8:=by omega
  calc
    (R.rho^d)^4=R.rho^(4*d):=by rw [←zpow_natCast,←zpow_mul];congr 1;ring
    _=R.rho^(8 : ℤ):=by rw [rho_zpow_mod,he]
    _= -1:=by simpa using R.rho_eight

/-- Full-support products of arbitrary fourth-root unaries are literal
Affine formulas; this creates no physical phase resource. -/
theorem unary_product_affine {m : ℕ} (q : Fin m→AlgebraicComplex)
    (fourth : ∀j,q j^4=1) : Affine (fun z : Word m=>∏j,if z j then q j else 1) := by
  classical
  choose e he using fun j=>fourthRootPhase_surjective_of_pow_four (fourth j)
  let Q : QuadraticPhase m:=⟨0,e,fun _ _=>0,fun _ _ _=>Or.inl rfl⟩
  convert affine_formula 1 (AffineSystem.unconstrained m) Q using 1
  funext z
  simp only [affineFormula,AffineSystem.unconstrained_holds,ite_true,one_mul,
    QuadraticPhase.eval,Q,zero_add,zero_mul,ite_self,Finset.sum_const_zero,add_zero,
    fourthRootPhase_sum]
  apply Finset.prod_congr rfl
  intro j _
  cases z j <;> simp [bitValue,he]

theorem seven_product (q : AlgebraicComplex) (fourth : q^4= -1) (x : Word 3) :
    (∏j : Fin 7,if C.codeSeven x j then q else 1)=A.phaseSeven x := by
  cases h0:x 0 <;> cases h1:x 1 <;> cases h2:x 2 <;>
    simp [C.codeSeven,A.phaseSeven,Fin.prod_univ_succ,h0,h1,h2]
  all_goals convert fourth using 1 <;> ring

theorem weight_formula (p : Fin n→P.Port 7) (a : AlgebraicComplex) (ha : a≠0)
    (z : Word 7) :
    a^(weight (P.word p z))=a^(weight (P.word p (fun _=>false)))*
      ∏j,if z j then a^(P.incidence p j) else 1 := by
  simpa [NoIPurePhaseRecipeFactor.factor,NoIPurePhaseRecipeFactor.total,
    Fin.prod_univ_one,Fin.sum_univ_one] using
    NoIPurePhaseRecipeFactor.formula (fun _ : Fin 1=>p) a ha z

/-- Exact physical weight factors into the universal cubic sign and a
proved Affine unary multiplier, retaining the original pinned scalar. -/
theorem corrected_affine (p : Fin n→P.Port 7) (a q : AlgebraicComplex)
    (ha : a≠0) (hq : q≠0) (qfour : q^4= -1)
    (fourth : ∀j,(a^(P.incidence p j)/q)^4=1) :
    Affine (fun x : Word 3=>a^(weight (P.word p (C.codeSeven x)))*A.phaseSeven x) := by
  let correction : Signature AlgebraicComplex 7:=
    fun z=>∏j,if z j then a^(P.incidence p j)/q else 1
  have hc:Affine correction:=unary_product_affine _ fourth
  have pull:=hc.precompose C.codeSeven codeSeven_affine
  have point (z : Word 7) :
      (∏j,if z j then a^(P.incidence p j) else 1)=
      (∏j,if z j then q else 1)*correction z := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    cases z j <;> simp only [Bool.false_eq_true,ite_false,ite_true,one_mul]
    field_simp
  convert pull.scale (a^(weight (P.word p (fun _=>false)))) using 1
  funext x
  rw [weight_formula p a ha,point,seven_product q qfour]
  calc
    _=a^(weight (P.word p (fun _=>false)))*
      (A.phaseSeven x*A.phaseSeven x)*correction (C.codeSeven x):=by ring
    _=_:=by rw [A.phaseSeven_square,mul_one]

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f 3)
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Word 3,Affine (minor D S z))

include minimal in
theorem source_general (bad : ¬Affine f) (p : Fin n→P.Port 7)
    (encoding : ∀x,P.word p (C.codeSeven x)=D.encode x)
    (a q : AlgebraicComplex) (ha : a≠0) (hq : q≠0) (qfour : q^4= -1)
    (fourth : ∀j,(a^(P.incidence p j)/q)^4=1) : Affine (twist a f) := by
  have corrected:=corrected_affine p a q ha hq qfour fourth
  have core:=A.phaseSeven_affine D minimal bad
  have reduced:Affine (fun x=>a^(weight (D.encode x))*D.reduced x):=by
    convert corrected.mul core using 1
    funext x
    rw [encoding]
    calc
      _=(a^(weight (D.encode x))*D.reduced x)*1:=by ring
      _=(a^(weight (D.encode x))*D.reduced x)*(A.phaseSeven x*A.phaseSeven x):=by
        rw [A.phaseSeven_square]
      _=_:=by ring
  let E : SystematicSupport (twist a f) 3:={
    ports:=D.ports
    injective:=D.injective
    encode:=D.encode
    affine:=D.affine
    free:=D.free
    supported x:=mul_ne_zero (pow_ne_zero _ ha) (D.supported x)
    covers x hx:=D.covers x (mul_ne_zero_iff.mp hx).2 }
  obtain ⟨S,hS⟩:=NoIPureClosedMinimal.support_system f
    (NoIPureClosedMinimal.chart_closed D) (NoIPureClosedMinimal.chart_nonzero D)
  apply E.affine_of_reduced S ?_ reduced
  intro x
  change S.Holds x↔a^(weight x)*f x≠0
  simpa only [mul_ne_zero_iff,and_iff_right (pow_ne_zero _ ha)] using hS x

include minimal in
/-- Every actual signed incidence is two modulo four. No square-affinity
hypothesis or caller-supplied phase classification is used. -/
theorem source (bad : ¬Affine f) (p : Fin n→P.Port 7)
    (encoding : ∀x,P.word p (C.codeSeven x)=D.encode x)
    (residue : ∀j,P.incidence p j%4=2) : Affine (twist R.rho f) := by
  apply source_general D minimal bad p encoding R.rho (R.rho^2)
    R.rho_nonzero (pow_ne_zero _ R.rho_nonzero) ?_ ?_
  · simpa only [←pow_mul] using R.rho_eight
  · intro j
    rw [div_pow,signed_two_fourth _ (residue j)]
    have h:(R.rho^2)^4= -1:=by simpa only [←pow_mul] using R.rho_eight
    rw [h]
    norm_num

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankThreeSource
end
