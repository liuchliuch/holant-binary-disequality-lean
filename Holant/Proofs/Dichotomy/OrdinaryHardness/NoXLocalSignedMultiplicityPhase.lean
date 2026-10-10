import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedProjection
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSimplexPhase

/-! Odd positive/negative multiplicities change the canonical opposite local
twist only by a full Affine coordinate gauge and a constant phase. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalSignedMultiplicityPhase
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXSeparateSignedProjection (signedCount)
end P
namespace F
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization (affine_prod)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n m : ℕ}
def unitPhase (b : Bool) : AlgebraicComplex := if b then zetaEight else 1
def count (p : Fin n→Port m) (q : Port m) : ℕ := ∑i,if p i=q then 1 else 0

theorem grouped {K : Type} [CommMonoid K] (p : Fin n→Port m) (g : Port m→K) :
    (∏i,g (p i))=∏q,g q^(count p q) := by
  rw [←Finset.prod_fiberwise' Finset.univ p g]
  apply Finset.prod_congr rfl
  intro q _
  rw [Finset.prod_const]
  congr 1
  simp only [count,Finset.card_filter]

def original (p : Fin n→Port m) (a x : Word m) : AlgebraicComplex :=
  ∏i,unitPhase (word p a i && word p x i)
def localFactor (a x : Word m) (j : Fin m) (b : Bool) : AlgebraicComplex :=
  unitPhase ((b ^^ a j) && (b ^^ x j))
def canonical (a x : Word m) : AlgebraicComplex := ∏j,∏b : Bool,localFactor a x j b
def constant (p : Fin n→Port m) : AlgebraicComplex := ∏b : Bool,unitPhase b^(count p (.inl b))
def gauge (p : Fin n→Port m) (a x : Word m) : AlgebraicComplex :=
  ∏j,∏b : Bool,(localFactor a x j b)^(P.signedCount p j b-1)

theorem original_grouped (p : Fin n→Port m) (a x : Word m) :
    original p a x=constant p*∏j,∏b : Bool,(localFactor a x j b)^(P.signedCount p j b) := by
  let g : Port m→AlgebraicComplex := fun q=>match q with
    | .inl b=>unitPhase b
    | .inr (j,b)=>localFactor a x j b
  have he : original p a x=∏i,g (p i) := by
    apply Finset.prod_congr rfl
    intro i _
    cases hq : p i with
    | inl b=>cases b <;> simp [OrdinaryNegativeSignedPortsCore.word,hq,g]
    | inr v=>rcases v with ⟨j,b⟩; simp [OrdinaryNegativeSignedPortsCore.word,hq,g,localFactor]
  rw [he,grouped]
  simp only [Fintype.prod_sum_type,Fintype.prod_prod_type,g,constant,localFactor,count,P.signedCount]

theorem split (p : Fin n→Port m) (odd : ∀j b,Odd (P.signedCount p j b)) (a x : Word m) :
    original p a x=constant p*(canonical a x*gauge p a x) := by
  rw [original_grouped,canonical,gauge,←Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro b _
  have positive : 0<P.signedCount p j b := by obtain ⟨k,hk⟩:=odd j b;omega
  rw [←pow_succ']
  congr 1
  omega

theorem even_fourth (c : ℕ) (odd : Odd c) : (zetaEight^(c-1))^4=1 := by
  have even : Even (c-1) := by obtain ⟨k,hk⟩:=odd;refine ⟨k,?_⟩;omega
  calc
    _=(zetaEight^4)^(c-1) := by rw [←pow_mul,←pow_mul];congr 1;omega
    _=1 := by rw [zetaEight_pow_four];simpa using even.neg_pow (1 : AlgebraicComplex)

theorem unitPhase_nonzero (b : Bool) : unitPhase b≠0 := by cases b <;> simp [unitPhase,zetaEight_ne_zero]

theorem gauge_affine (p : Fin n→Port m) (odd : ∀j b,Odd (P.signedCount p j b)) (a : Word m) :
    Affine (gauge p a) := by
  apply F.affine_prod
  intro j
  apply F.affine_prod
  intro b
  let value (t : Bool) := unitPhase ((b ^^ a j) && (b ^^ t))^(P.signedCount p j b-1)
  have fourth (t : Bool) : value t^4=1 := by
    dsimp only [value]
    cases hc : (b ^^ a j) && (b ^^ t)
    · simp [unitPhase]
    · exact even_fourth _ (odd j b)
  have hu := GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers j
    (value false) (value true) (pow_ne_zero _ (unitPhase_nonzero _))
    ((fourth false).trans (fourth true).symm)
  have he : (fun x : Word m=>(localFactor a x j b)^(P.signedCount p j b-1))=
      (fun x : Word m=>if x j then value true else value false) := by
    funext x
    cases hx : x j <;> simp [localFactor,value,hx]
  rw [he]
  exact hu


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXLocalSignedMultiplicityPhase
end
