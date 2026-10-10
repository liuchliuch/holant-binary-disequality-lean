import Holant.Proofs.Dichotomy.Retained.StableDenseResidualGaugeCore
import Holant.Proofs.Dichotomy.Retained.StableDenseResidualAlgebra

/-! Coefficient factorization of the actual residual predicate. The pure
algebra is checked independently of the original-source programme imports.
The unary factors are semantic coefficients, not freely available gadgets. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGauge
open Holant Holant.Tractable Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped BigOperators
variable {K : Type} [Field K]

abbrev weighted (a : K) (u : Fin 4→K) : Signature K 4 := StableDenseResidualGaugeCore.weighted a u

theorem products_iff (M : Signature K 4) : StableDenseResidualAlgebra.Products M ↔
    StableDenseResidualGaugeCore.Products M := Iff.rfl

theorem weighted_products (a : K) (u : Fin 4→K) :
    StableDenseResidualAlgebra.Products (weighted a u) :=
  StableDenseResidualGaugeCore.weighted_products a u

theorem weighted_value (a : K) (u : Fin 4→K) (x : Fin 4→Bool) :
    weighted a u x=if weight x%2=0 then a*∏i,if x i then u i else 1 else 0 :=
  StableDenseResidualGaugeCore.weighted_value a u x

theorem factor_with_root (M : Signature K 4) (he : EvenSupport M)
    (hp : StableDenseResidualAlgebra.Products M)
    (ha : (entries M).a≠0) (hb : (entries M).b≠0) (hc : (entries M).c≠0)
    (hd : (entries M).d≠0) (t : K) (ht : t≠0)
    (hsq : t^2=(entries M).b*(entries M).c/((entries M).a*(entries M).d)) :
    M=weighted (entries M).a
      ![(entries M).w/((entries M).a*t),(entries M).c/((entries M).a*t),
        (entries M).b/((entries M).a*t),t] :=
  StableDenseResidualGaugeCore.factor_with_root M he hp ha hb hc hd t ht hsq

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseResidualGauge
