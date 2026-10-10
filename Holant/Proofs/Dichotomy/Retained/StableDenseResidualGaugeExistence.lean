import Holant.Proofs.Dichotomy.Retained.StableDenseResidualGauge

/-! Existence of a nonzero unary coefficient factorization on the dense
residual locus. This is a semantic description, not oracle access to unaries
and not a tractability conclusion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeExistence
open Holant Holant.Tractable Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace G
export StableDenseResidualGauge (weighted factor_with_root)
end G
variable {K : Type} [Field K] [IsAlgClosed K]

theorem exists_factor (M : Signature K 4) (he : EvenSupport M)
    (hp : StableDenseResidualAlgebra.Products M)
    (ha : (entries M).a≠0) (hb : (entries M).b≠0) (hc : (entries M).c≠0)
    (hd : (entries M).d≠0) (hw : (entries M).w≠0) :
    ∃u : Fin 4→K, (∀i,u i≠0) ∧ M=G.weighted (entries M).a u := by
  obtain ⟨t,ht⟩ := IsAlgClosed.exists_pow_nat_eq
    ((entries M).b*(entries M).c/((entries M).a*(entries M).d)) (by decide : 0<2)
  have htn : t≠0 := by
    intro hz
    rw [hz,zero_pow (by decide : 2≠0)] at ht
    exact div_ne_zero (mul_ne_zero hb hc) (mul_ne_zero ha hd) ht.symm
  refine ⟨![(entries M).w/((entries M).a*t),(entries M).c/((entries M).a*t),
    (entries M).b/((entries M).a*t),t],?_,G.factor_with_root M he hp ha hb hc hd t htn ht⟩
  intro i
  fin_cases i
  · exact div_ne_zero hw (mul_ne_zero ha htn)
  · exact div_ne_zero hc (mul_ne_zero ha htn)
  · exact div_ne_zero hb (mul_ne_zero ha htn)
  · exact htn

theorem algebraic_factor (M : Signature AlgebraicComplex 4) (he : EvenSupport M)
    (hp : StableDenseResidualAlgebra.Products M)
    (ha : (entries M).a≠0) (hb : (entries M).b≠0) (hc : (entries M).c≠0)
    (hd : (entries M).d≠0) (hw : (entries M).w≠0) :
    ∃u : Fin 4→AlgebraicComplex, (∀i,u i≠0) ∧ M=G.weighted (entries M).a u := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  exact exists_factor M he hp ha hb hc hd hw

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGaugeExistence
