import Holant.Proofs.Hardness.EOBinaryPlaneClassification

/-! The two literal opposite-pair restrictions of a mating tensor already
force its Gram equalities. No dichotomy or hardness conclusion is a premise. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedCriterion
open Holant Holant.Tractable
namespace B
export EOBinaryPlaneClassification (kernel_table)
end B
namespace P
export Holant.Tractable.SymmetricBinaryPullback (table product_shape)
end P
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem norm_of_fourth {a b : AlgebraicComplex} (h : a^4=b^4) : ‖(a : ℂ)‖=‖(b : ℂ)‖ := by
  have hh := congrArg (fun z : AlgebraicComplex => ‖(z : ℂ)‖) h
  change ‖(a : ℂ)^4‖=‖(b : ℂ)^4‖ at hh
  simp only [norm_pow] at hh
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : 4≠0)).mp hh

theorem binary_pair_norm (f : Signature AlgebraicComplex 2)
    (ha : f ![false,false]≠0) (hb : f ![false,true]≠0)
    (hcross : f ![true,false]=f ![false,true])
    (hdiag : ‖(f ![true,true] : ℂ)‖=‖(f ![false,false] : ℂ)‖)
    (ht : Affine f ∨ Product f) :
    ‖(f ![false,false] : ℂ)‖=‖(f ![false,true] : ℂ)‖ := by
  rcases ht with h|h
  · exact norm_of_fourth (h.fourth_power_eq _ _ ha hb)
  · have hs := P.product_shape (E:=P.table f) (by simpa only [B.kernel_table] using h)
    rcases hs with hs|hs|hs
    · exact False.elim (hb hs.1)
    · exact False.elim (ha hs.1)
    · change f ![false,false]*f ![true,true] = f ![false,true]*f ![true,false] at hs
      have hh := congrArg (fun z : AlgebraicComplex => ‖(z : ℂ)‖) hs
      change ‖(f ![false,false] : ℂ)*(f ![true,true] : ℂ)‖ =
        ‖(f ![false,true] : ℂ)*(f ![true,false] : ℂ)‖ at hh
      simp only [norm_mul,hdiag,hcross] at hh
      nlinarith [norm_nonneg (f ![false,false] : ℂ),norm_nonneg (f ![false,true] : ℂ)]

def crossingPairing : OrientedPerfectPairing 4 where
  count := 2
  ports := {
    toFun p := if p.1=0 then (if p.2 then 2 else 0) else (if p.2 then 3 else 1)
    invFun := ![(0,false),(1,false),(0,true),(1,true)]
    left_inv := by decide
    right_inv := by decide }

theorem crossing_word (x : Fin 2 → Bool) :
    crossingPairing.word x = ![x 0,x 1,!(x 0),!(x 1)] := by
  funext i
  fin_cases i <;> rfl

theorem pairing_tract (M : Signature AlgebraicComplex 4)
    (h : EOTract {⟨4,M⟩}) (p : OrientedPerfectPairing 4) :
    Affine (p.restrict M) ∨ Product (p.restrict M) := by
  obtain ⟨_,_,_,cl,_,hc⟩ := h
  have hh := hc ⟨4,M⟩ (by simp) p
  cases cl
  · exact Or.inl hh
  · exact Or.inr hh

variable (M : Signature AlgebraicComplex 4)
variable (symA : M ![true,true,false,false]=M ![false,false,true,true])
variable (symB : M ![true,false,false,true]=M ![false,true,true,false])
variable (symC : ‖(M ![true,false,true,false] : ℂ)‖=‖(M ![false,true,false,true] : ℂ)‖)
variable (ltAB : ‖(M ![false,false,true,true] : ℂ)‖ < ‖(M ![false,true,true,false] : ℂ)‖)
variable (ht : EOTract {⟨4,M⟩})

include symA symB ltAB ht in
theorem same_zero : M ![false,false,true,true]=0 := by
  by_contra ha
  have hb : M ![false,true,true,false]≠0 := by
    intro h
    simp only [h,ZeroMemClass.coe_zero,norm_zero] at ltAB
    exact (not_lt_of_ge (norm_nonneg _)) ltAB
  have h := binary_pair_norm (crossingPairing.restrict M)
    (by simpa [OrientedPerfectPairing.restrict,crossing_word] using ha)
    (by simpa [OrientedPerfectPairing.restrict,crossing_word] using hb)
    (by simpa [OrientedPerfectPairing.restrict,crossing_word] using symB)
    (by simp [OrientedPerfectPairing.restrict,crossing_word,symA])
    (pairing_tract M ht crossingPairing)
  exact (ne_of_lt ltAB) (by simpa [OrientedPerfectPairing.restrict,crossing_word] using h)

include symB symC ltAB ht in
theorem cross_saturated (hc : M ![false,true,false,true]≠0) :
    ‖(M ![false,true,false,true] : ℂ)‖=‖(M ![false,true,true,false] : ℂ)‖ := by
  have hb : M ![false,true,true,false]≠0 := by
    intro h
    simp only [h,ZeroMemClass.coe_zero,norm_zero] at ltAB
    exact (not_lt_of_ge (norm_nonneg _)) ltAB
  simpa [EOBinaryPlaneCore.restrict_eq,EOBinaryPlaneCore.compress,EOBinaryPlaneCore.word] using
    binary_pair_norm (EOBinaryPlaneCore.pairing.restrict M)
      (by simpa [EOBinaryPlaneCore.restrict_eq,EOBinaryPlaneCore.compress,EOBinaryPlaneCore.word] using hc)
      (by simpa [EOBinaryPlaneCore.restrict_eq,EOBinaryPlaneCore.compress,EOBinaryPlaneCore.word] using hb)
      (by simpa [EOBinaryPlaneCore.restrict_eq,EOBinaryPlaneCore.compress,EOBinaryPlaneCore.word] using symB)
      (by simpa [EOBinaryPlaneCore.restrict_eq,EOBinaryPlaneCore.compress,EOBinaryPlaneCore.word] using symC)
      (pairing_tract M ht EOBinaryPlaneCore.pairing)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedCriterion
