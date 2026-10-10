import Holant.ReedMuller.WeightTwoIntegration.ThreeSquares
import Holant.ReedMuller.WeightTwoIntegration.Factorization

/-! The kappa=1 three-pair branch gives the same genuine original-basis
factorization as the higher-arity product branch. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.MatchingConsistency
open scoped BigOperators

 theorem exceptionalH_one (rho : Fin 3 → ℂ) (a b c : Bool) :
    exceptionalH rho 1 a b c=rho 0^(if a then 1 else 0 : ℕ)*
      rho 1^(if b then 1 else 0 : ℕ)*rho 2^(if c then 1 else 0 : ℕ) := by
  cases a <;> cases b <;> cases c <;> simp [exceptionalH]

 theorem three_product {r : ℕ} (hc : r=3) (h : Signature ℂ r) (rho : Fin 3 → ℂˣ) (kap : ℂˣ)
    (hk : (kap:ℂ)=1)
    (he : ∀a b c,h (fun i=>![a,b,c] (Fin.cast hc i))=h (fun _=>false)*
      exceptionalH (fun i=>(rho i:ℂ)) kap a b c) :
    ∃rho' : Fin r → ℂˣ,∀t,h t=h (fun _=>false)*∏i,(rho' i:ℂ)^(if t i then 1 else 0 : ℕ) := by
  subst r
  refine ⟨rho,?_⟩
  intro t
  have hh := he (t 0) (t 1) (t 2)
  simp only [Fin.cast_refl] at hh
  change h ![t 0,t 1,t 2]=_ at hh
  rw [←three_word_eta t] at hh
  rw [hk,exceptionalH_one] at hh
  simpa only [Fin.prod_univ_three] using hh

 theorem OriginalPairing.three_factor {n : ℕ} (q : Signature ℂ n) (hq : q≠0)
    (C : OriginalPairing (CoefficientAtlas.walsh q)) (hc : C.count=3)
    (H : Consistent (CoefficientAtlas.walsh q)) (hd : EqualityDeck (CoefficientAtlas.walsh q)) (hn : 6≤n)
    (rho : Fin 3 → ℂˣ) (kap : ℂˣ) (hk : (kap:ℂ)=1)
    (he : ∀a b c,C.threeLogical hc ![a,b,c]=C.logical (fun _=>false)*
      exceptionalH (fun i=>(rho i:ℂ)) kap a b c) : Pauli.ExoticKlein.Fiber.HasProperTensorFactor q := by
  obtain ⟨rho',hrho⟩ := three_product hc C.logical rho kap hk he
  apply C.physical_factor q hq (by norm_num) H hd hn rho'
  intro t
  apply Units.ext
  simp only [OriginalPairing.normalizedLogical,Units.val_div_eq_div_val,Units.val_mk0,
    Units.coe_prod,Units.val_pow_eq_pow_val]
  exact (div_eq_iff (C.logical_nonzero (by norm_num) H hd hn _)).mpr ((hrho t).trans (mul_comm _ _))

end Holant.ReedMuller.WeightTwoIntegration
