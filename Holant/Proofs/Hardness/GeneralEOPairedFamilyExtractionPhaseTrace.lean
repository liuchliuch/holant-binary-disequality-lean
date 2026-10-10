import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPhaseMinor

/-! Summing one variable of every nontrivial fourth-root ternary monomial
produces an actual nonaffine, nonproduct binary, including the cancelling
minus-one case. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseTrace
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace B
export EOBinaryPlaneClassification (Full full_affine_iff full_product_iff)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable (δ : AlgebraicComplex)

def monomial : Signature AlgebraicComplex 3 := fun z => if z=![true,true,true] then δ else 1

def binary : Signature AlgebraicComplex 2 := fun z => if z 0 && z 1 then 1+δ else 2

theorem trace (z : Fin 2 → Bool) :
    monomial δ ![z 0,z 1,false]+monomial δ ![z 0,z 1,true]=binary δ z := by
  cases h0 : z 0 <;> cases h1 : z 1 <;> norm_num [monomial,binary,h0,h1]

theorem not_product (hn : δ≠1) : ¬Product (binary δ) := by
  intro hp
  have hs := Holant.Tractable.SymmetricBinaryPullback.product_shape
    (E:=Holant.Tractable.SymmetricBinaryPullback.table (binary δ))
    (by simpa only [EOBinaryPlaneClassification.kernel_table] using hp)
  rcases hs with hs|hs|hs
  · norm_num [Holant.Tractable.SymmetricBinaryPullback.table,binary] at hs
  · norm_num [Holant.Tractable.SymmetricBinaryPullback.table,binary] at hs
  · apply hn
    have he : 2*(1+δ)=2*2 := hs
    linear_combination he/2

theorem not_affine_minus : ¬Affine (binary (-1)) := by
  intro h
  have hh := affine_support_xor3 h ![false,false] ![false,true] ![true,false]
    (by norm_num [binary]) (by norm_num [binary]) (by norm_num [binary])
  have he : xor3 (![false,false] : Fin 2→Bool) ![false,true] ![true,false]=![true,true] := by decide
  norm_num [he,binary] at hh

theorem not_affine_square_minus (hsq : δ^2=-1) : ¬Affine (binary δ) := by
  have hne : 1+δ≠0 := by
    intro h
    have he : δ=-1 := by linear_combination h
    rw [he] at hsq
    norm_num at hsq
  have hpow : (1+δ)^4=-4 := by
    calc
      (1+δ)^4=(1+2*δ+δ^2)^2 := by ring
      _=-4 := by rw [hsq]; ring_nf; rw [hsq]; norm_num
  intro h
  have hh := h.fourth_power_eq ![true,true] ![false,false]
    (by simpa [binary] using hne) (by norm_num [binary])
  change (1+δ)^4=2^4 at hh
  rw [hpow] at hh
  norm_num at hh

theorem not_affine (hfour : δ^4=1) (hn : δ≠1) : ¬Affine (binary δ) := by
  have hsq : (δ^2)^2=1 := by simpa only [←pow_mul] using hfour
  rcases sq_eq_one_iff.mp hsq with hsq|hsq
  · rcases sq_eq_one_iff.mp hsq with he|he
    · exact False.elim (hn he)
    · rw [he]
      exact not_affine_minus
  · exact not_affine_square_minus δ hsq

theorem not_tract (hfour : δ^4=1) (hn : δ≠1) :
    ¬EOTract {⟨4,EOBinaryPlaneCore.lift (binary δ)⟩} := by
  rw [EOBinaryPlaneTract.lift_tract_iff]
  exact not_or.mpr ⟨not_affine δ hfour hn,not_product δ hn⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseTrace
