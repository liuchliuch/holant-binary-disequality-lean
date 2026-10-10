import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryFiniteValues
import Holant.Proofs.Hardness.EOBinaryPlaneGramGraphComplex
import Holant.Proofs.Hardness.EOBinaryPlanePositive

/-! A common positive coefficient power realizes complex conjugation up to
one exact nonzero scalar. The nonsingular positive Gram criterion then
excludes equal norms for all coefficients of the physical Gram output. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryConjugate
open Holant Holant.Tractable
namespace F
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFlat (norm_product)
end F
namespace G
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGram (table cross determinant table_determinant)
end G
namespace P
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePositive (Good)
end P
namespace X
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGramGraphComplex (matrix output_star output_matrix)
end X
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false

def gram (f : Signature ℂ 2) : Signature ℂ 2:=fun x=>∑v : Bool,f ![x 0,v]*star (f ![x 1,v])
def normTable (f : Signature ℂ 2) : Signature ℝ 2:=
  G.table (f ![false,false]) (f ![false,true]) (f ![true,false]) (f ![true,true])

theorem positive_power (f : Signature ℂ 2) (full : ∀x,f x≠0) (n : ℕ) (hn : 2≤n)
    (powers : ∀x,f x^n=f ![false,false]^n) :
    ∃c : ℂ,c≠0 ∧ ∀x,f x^(n-1)=c*star (f x) := by
  let a:=f ![false,false]
  let c:=a^n/(a*star a)
  have an : a≠0:=full _
  have denom : a*star a≠0:=mul_ne_zero an (star_ne_zero.mpr an)
  refine ⟨c,div_ne_zero (pow_ne_zero _ an) denom,?_⟩
  intro x
  have norms:=NoIOrdinaryFiniteValues.complex_norm_of_power (by omega : n≠0) (powers x)
  have product : f x*star (f x)=a*star a := by rw [F.norm_product,F.norm_product,norms]
  apply mul_left_cancel₀ (full x)
  calc
    f x*f x^(n-1)=f x^n := by rw [←pow_succ'];congr 1;omega
    _=a^n:=powers x
    _=c*(a*star a):=(div_mul_cancel₀ _ denom).symm
    _=f x*(c*star (f x)):=by rw [←product];ring

theorem gram_norm (f : Signature ℂ 2) (x : Fin 2→Bool) :
    Complex.normSq (gram f x)=normTable f x := by
  have literal : X.matrix (f ![false,false]) (f ![false,true]) (f ![true,false]) (f ![true,true])=f := by
    funext z
    have word : z=![z 0,z 1] := by funext i;fin_cases i <;> rfl
    rw [word]
    cases z 0 <;> cases z 1 <;> rfl
  have h:=congrFun (X.output_matrix (f ![false,false]) (f ![false,true]) (f ![true,false]) (f ![true,true])) x
  rw [literal,X.output_star] at h
  exact Complex.ofReal_injective h

theorem good_nonproduct (f : Signature AlgebraicComplex 2)
    (good : P.Good (normTable (fun x=>(f x : ℂ)))) : ¬Product f := by
  intro product
  have shape:=SymmetricBinaryPullback.product_shape (E:=SymmetricBinaryPullback.table f) (by
    convert product using 1
    funext x
    apply congrArg f
    funext i;fin_cases i <;> rfl)
  change (f ![false,true]=0 ∧ f ![true,false]=0) ∨
    (f ![false,false]=0 ∧ f ![true,true]=0) ∨
    f ![false,false]*f ![true,true]=f ![false,true]*f ![true,false] at shape
  rcases shape with ⟨hb,hc⟩|⟨ha,hd⟩|det
  · have positive:=good.1 ![false,true]
    simpa [normTable,G.table,G.cross,hb,hc] using positive
  · have positive:=good.1 ![false,true]
    simpa [normTable,G.table,G.cross,ha,hd] using positive
  · have zero : G.determinant (f ![false,false]) (f ![false,true]) (f ![true,false]) (f ![true,true])=0 := by
      change (f ![false,false] : ℂ)*(f ![true,true] : ℂ)-(f ![false,true] : ℂ)*(f ![true,false] : ℂ)=0
      exact sub_eq_zero.mpr (congrArg (fun z : AlgebraicComplex=>(z : ℂ)) det)
    have positive:=good.2
    rw [normTable,G.table_determinant,zero] at positive
    simpa using positive

theorem gram_full (f : Signature ℂ 2) (good : P.Good (normTable f)) : ∀x,gram f x≠0 := by
  intro x zero
  have positive:=good.1 x
  rw [←gram_norm,zero,Complex.normSq_zero] at positive
  exact (lt_irrefl _ positive)

theorem gram_not_flat (f : Signature ℂ 2) (good : P.Good (normTable f)) :
    ¬(∀x,Complex.normSq (gram f x)=Complex.normSq (gram f ![false,false])) := by
  intro flat
  have equal (x : Fin 2→Bool) : normTable f x=normTable f ![false,false] := by
    simpa only [gram_norm] using flat x
  have positive:=good.2
  rw [equal ![true,true],equal ![false,true],equal ![true,false],sub_self] at positive
  exact lt_irrefl _ positive


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryConjugate
end
