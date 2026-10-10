import Holant.ReedMuller.WeightTwoIntegration.WeightedDeck

/-! A literal two-variable restriction of a supported weighted matching has
zero determinant when each original port depends on only one variable. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant
open scoped BigOperators
variable {K ι : Type*} [Field K]

 theorem WeightedProduct.separable_minor (P : WeightedProduct K ι) (y : Bool → Bool → ι → Bool)
    (hn : ∀a b,P.value (y a b)≠0)
    (hsep : ∀p,(∀a b,y a b p=y a false p) ∨ (∀a b,y a b p=y false b p)) :
    P.value (y false false)*P.value (y true true)-
      P.value (y false true)*P.value (y true false)=0 := by
  have he (e : Fin P.edges) :
      (P.diagonal e (y false false (P.ports (e,false))):K)*
          (P.diagonal e (y true true (P.ports (e,false))):K)=
      (P.diagonal e (y false true (P.ports (e,false))):K)*
          (P.diagonal e (y true false (P.ports (e,false))):K) := by
    rcases hsep (P.ports (e,false)) with h | h
    · rw [h true true,h false true]
    · rw [h true true,h true false]
      ring
  simp_rw [P.value_eq_diagonal _ (hn _ _),WeightedProduct.diagonalValue,Units.val_mul,Units.coe_prod]
  calc
    _=(P.scalar:K)^2*(∏e,(P.diagonal e (y false false (P.ports (e,false))):K)*
          (P.diagonal e (y true true (P.ports (e,false))):K))-
        (P.scalar:K)^2*(∏e,(P.diagonal e (y false true (P.ports (e,false))):K)*
          (P.diagonal e (y true false (P.ports (e,false))):K)) := by
      simp only [Finset.prod_mul_distrib]
      ring
    _=0 := by simp_rw [he]; ring

end Holant.ReedMuller.WeightTwoIntegration
