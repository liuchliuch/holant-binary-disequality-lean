import Holant.ReedMuller.SupportReconstruction.Cards

/-! The quotient of the two actual matching cards is the parity character.
It is reconstructed from literal singleton coefficients, not assumed. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
variable {K ι : Type*} [Field K] [DecidableEq ι]
set_option backward.isDefEq.respectTransparency false

 def singletonWord {r : ℕ} (e : Fin r) : Fin r → Bool := fun d=>decide (d=e)
 def minusUnit : Kˣ := Units.mk0 (-1:K) (neg_ne_zero.mpr one_ne_zero)
 def quotient (P Q : WeightedProduct K ι) (t : Fin P.edges → Bool) : Kˣ :=
  Q.diagonalValue (logicalWord P t)/P.diagonalValue (logicalWord P t)

 theorem singleton_logical (P : WeightedProduct K ι) (e : Fin P.edges) :
    logicalWord P (singletonWord e)=pairIndicator (P.ports (e,false)) (P.ports (e,true)) := by
  funext p
  obtain ⟨⟨d,b⟩,rfl⟩ := P.ports.surjective p
  cases b <;> simp [logicalWord,singletonWord,pairIndicator,P.ports.injective.eq_iff]

 theorem quotient_product (P Q : WeightedProduct K ι) (t : Fin P.edges → Bool) :
    quotient P Q t/quotient P Q (fun _=>false)=
      ∏i, (quotient P Q (singletonWord i)/quotient P Q (fun _=>false))^(if t i then 1 else 0 : ℕ) := by
  classical
  let label : Fin Q.edges ⊕ Fin P.edges → Fin P.edges :=
    Sum.elim (fun e=>(P.ports.symm (Q.ports (e,false))).1) id
  let a : Fin Q.edges ⊕ Fin P.edges → Bool → Kˣ :=
    Sum.elim Q.diagonal (fun e b=>(P.diagonal e b)⁻¹)
  let c := Q.scalar/P.scalar
  have he (x : Fin P.edges → Bool) : quotient P Q x=c*∏e,a e (x (label e)) := by
    simp only [quotient,WeightedProduct.diagonalValue,logicalWord,c,Fintype.prod_sum_type,
      a,label,Sum.elim_inl,Sum.elim_inr,id_eq,Equiv.symm_apply_apply,Finset.prod_inv_distrib]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ac_rfl
  have hh := indexed_normalized_product c a label t
  rw [←he t] at hh
  have hz : quotient P Q (fun _=>false)=c*∏e,a e false := he _
  rw [←hz] at hh
  have hs (i : Fin P.edges) : quotient P Q (singletonWord i)=c*∏e,a e (decide (label e=i)) := he _
  simp only [←hs] at hh
  exact hh

 namespace MatchingCards
 variable {f : Tensor K ι} {i j : ι} (D : MatchingCards f i j)

 theorem quotient_value (t : Fin D.plus.edges → Bool) :
    (quotient D.plus D.minus t:K)=D.minus.value (logicalWord D.plus t)/D.plus.value (logicalWord D.plus t) := by
  rw [quotient,Units.val_div_eq_div_val,
    D.minus.value_eq_diagonal _ (D.minus_logical_nonzero t),
    D.plus.value_eq_diagonal _ (logical_supported D.plus t)]

 theorem quotient_zero (htwo : (2:K)≠0) : quotient D.plus D.minus (fun _=>false)=1 := by
  apply Units.ext
  rw [D.quotient_value]
  change D.minus.value (fun _=>false)/D.plus.value (fun _=>false)=1
  rw [D.plus_zero,D.minus_zero,div_self htwo]

 theorem quotient_singleton (hW : weightGraph f=⊥) (e : Fin D.plus.edges) :
    quotient D.plus D.minus (singletonWord e)=minusUnit := by
  let p := D.plus.ports (e,false)
  let q := D.plus.ports (e,true)
  have hpq : p≠q := by
    intro hh
    have hb := congrArg Prod.snd (D.plus.ports.injective hh)
    cases hb
  have hv : p.val≠q.val := fun hh=>hpq (Subtype.ext hh)
  have hs := card_add f i j (logicalWord D.plus (singletonWord e))
  rw [singleton_logical,sameLift_pair,pair_coefficient_zero f hW p.val q.val hv,mul_zero] at hs
  rw [D.plus_eq,D.minus_eq] at hs
  apply Units.ext
  rw [D.quotient_value]
  change D.minus.value (logicalWord D.plus (singletonWord e))/D.plus.value (logicalWord D.plus (singletonWord e))=(-1:K)
  apply (div_eq_iff (logical_supported D.plus (singletonWord e))).mpr
  rw [singleton_logical]
  linear_combination hs

 theorem quotient_parity (htwo : (2:K)≠0) (hW : weightGraph f=⊥) (t : Fin D.plus.edges → Bool) :
    quotient D.plus D.minus t=∏e,(minusUnit:Kˣ)^(if t e then 1 else 0 : ℕ) := by
  have hh := quotient_product D.plus D.minus t
  rw [D.quotient_zero htwo,div_one] at hh
  simpa only [D.quotient_singleton hW,div_one] using hh

 theorem minus_parity (htwo : (2:K)≠0) (hW : weightGraph f=⊥) (t : Fin D.plus.edges → Bool) :
    D.minus.value (logicalWord D.plus t)=
      (∏e,(-1:K)^(if t e then 1 else 0 : ℕ))*D.plus.value (logicalWord D.plus t) := by
  have hh := congrArg (fun a : Kˣ=>(a:K)) (D.quotient_parity htwo hW t)
  rw [D.quotient_value] at hh
  simp only [Units.coe_prod,Units.val_pow_eq_pow_val,minusUnit,Units.val_mk0] at hh
  exact (div_eq_iff (logical_supported D.plus t)).mp hh

 end MatchingCards
end Holant.ReedMuller.SupportReconstruction
