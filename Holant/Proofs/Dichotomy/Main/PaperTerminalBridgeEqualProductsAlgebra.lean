import Holant.Proofs.Hardness.EightVertexGaugePorts
import Holant.Proofs.Dichotomy.Retained.StableDenseResidualGaugeExistence
import Holant.EightVertex.ProductAnchor.Source

/-! The full-support equal-opposite-product branch. Equal port-weight squares
are the native-compatible dense product-anchor form. A separated square pair
has a literal two-copy X-network with unequal sector products, unless its odd
sector vanishes and exposes two nonsingular diagonal tensor factors. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsAlgebra
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open scoped BigOperators
namespace G
export StableDenseResidualGaugeCore (Products weighted weighted_value)
end G
namespace T
export EightVertexGaugeTwoRowAlgebra (evenFactor oddFactor output products_iff self_crossed_factor
  diagonalTensor odd_zero_product)
end T
namespace P
export EightVertexGaugePorts (zeroPair onPorts_output)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]

theorem even_live (u : Fin 4→K) (live : ∀i,u i≠0) : T.evenFactor u u≠0 := by
  have eqn : T.evenFactor u u=2*u 2*u 3 := by unfold T.evenFactor;ring
  rw [eqn]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (live 2)) (live 3)

theorem square_separation (a : K) (u : Fin 4→K) (scale : a≠0) (live : ∀i,u i≠0)
    (different : u 2^2≠u 3^2) : ¬G.Products (T.output a a u u true) := by
  intro products
  have eqn := (T.products_iff a a u u true scale scale live live).mp products
  have defect := T.self_crossed_factor u
  rw [eqn,sub_self] at defect
  have squared : (u 2^2-u 3^2)^2=0 := by linear_combination defect
  exact different (sub_eq_zero.mp (sq_eq_zero_iff.mp squared))

theorem output_dense (a : K) (u : Fin 4→K) (scale : a≠0) (live : ∀i,u i≠0)
    (oddLive : T.oddFactor u u true≠0) : StableDenseParityAlgebra.Dense (T.output a a u u true) := by
  have evenLive := even_live u live
  simp [StableDenseParityAlgebra.Dense,entries,T.output,table,scale,live,evenLive,oddLive]

theorem output_even (a : K) (u : Fin 4→K) : EvenSupport (T.output a a u u true) := by
  intro x odd
  rw [word_eta x] at odd ⊢
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    first | exact (odd (by simp only [h0,h1,h2,h3];decide)).elim | rfl

theorem separated_pair (u : Fin 4→K) (different : ¬∀i,u i^2=u 0^2) :
    ∃k : Fin 3,u ((P.zeroPair k).symm 2)^2≠u ((P.zeroPair k).symm 3)^2 := by
  by_contra! none
  have h01 : u 0^2=u 1^2 := by simpa [P.zeroPair] using none 0
  have h02 : u 0^2=u 2^2 := by simpa [P.zeroPair] using none 1
  have h03 : u 0^2=u 3^2 := by simpa [P.zeroPair] using none 2
  apply different
  intro i
  fin_cases i
  · rfl
  · exact h01.symm
  · exact h02.symm
  · exact h03.symm

theorem same_squares_dense (a : AlgebraicComplex) (u : Fin 4→AlgebraicComplex)
    (scale : a≠0) (live : ∀i,u i≠0) (same : ∀i,u i^2=u 0^2) :
    Holant.EightVertex.ProductAnchor.DenseForm (G.weighted a u) := by
  classical
  have signs : ∀i,∃b : Bool,u i=if b then -(u 0) else u 0 := by
    intro i
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (same i) with h|h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  choose s hs using signs
  refine ⟨a,u 0,scale,live 0,s,?_⟩
  intro x
  rw [G.weighted_value]
  have factors (i : Fin 4) : (if x i then u i else 1)=
      (u 0)^(if x i then 1 else 0 : ℕ)*(-1:AlgebraicComplex)^(if s i && x i then 1 else 0 : ℕ) := by
    rw [hs i]
    cases x i <;> cases s i <;> simp
  simp_rw [factors]
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum]
  simp only [weight,Holant.EightVertex.ProductAnchor.bitSign,mul_assoc]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeEqualProductsAlgebra
end
