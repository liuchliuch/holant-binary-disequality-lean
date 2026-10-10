import Holant.Proofs.Hardness.GeneralEOARSNonclosedPrefix
import Holant.Proofs.Hardness.GeneralEODEQProducerNormalize

/-! A negative covariance pair gives an actual hard quaternary, an isolated
antipodal quaternary, or the retained free-pair support branch. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedSplit
open Holant Holant.Tractable
namespace P
export GeneralEOARSNonclosedPrefix (complex inclusion output_map correlation_prefix free_prefix)
end P
namespace C
export GeneralEOARSNonclosedCoefficients
  (row diagonal_norm cross_norm cross_complement_norm row_mass_nonneg)
end C
namespace G
export GeneralEOARSNonclosedGram (rowMass rowInner)
end G
namespace M
export GeneralEOARSNonclosedMating (output network denote central output_swap)
end M
namespace V
export GeneralEOARSNonclosedMass (correlation mass)
end V
namespace R
export GeneralEOARSNonclosedCriterion (same_zero cross_saturated)
end R
namespace S
export GeneralEOARSNonclosedSupport (FreePair)
end S
namespace D
export GeneralEODEQProducerCore (Pair)
end D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

private theorem six_words : ∀x : Fin 4 → Bool, 2*weight x=4 →
    x=![false,false,true,true] ∨ x=![false,true,false,true] ∨
    x=![false,true,true,false] ∨ x=![true,false,false,true] ∨
    x=![true,false,true,false] ∨ x=![true,true,false,false] := by decide

theorem isolated (Q : Signature AlgebraicComplex 4) (he : Signature.CentralSupport Q)
    (hA : Q ![false,false,true,true]=0) (hC : Q ![false,true,false,true]=0)
    (hD : Q ![true,false,true,false]=0) (hF : Q ![true,true,false,false]=0)
    (hB : Q ![false,true,true,false]≠0) (hE : Q ![true,false,false,true]≠0) :
    Nonempty (D.Pair Q) := by
  refine ⟨⟨![false,true,true,false],![true,false,false,true],hB,hE,by decide,?_⟩⟩
  intro x hx _
  have hw : 2*weight x=4 := by by_contra hw; exact hx (he x hw)
  rcases six_words x hw with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all

theorem split (f : Signature AlgebraicComplex (n+2))
    (he : Signature.CentralSupport f)
    (hf : GeneralEOARSBoundary.ARSUpToScale (P.complex f))
    (negative : V.correlation (V.mass (P.complex f)) 0 1<0) :
    ¬EOTract {⟨4,M.output (K:=AlgebraicComplex) f⟩} ∨ Nonempty (D.Pair (M.output (K:=AlgebraicComplex) f)) ∨ S.FreePair f 0 1 := by
  classical
  by_cases ht : EOTract {⟨4,M.output (K:=AlgebraicComplex) f⟩}
  swap
  · exact Or.inl ht
  right
  have symA : M.output (K:=AlgebraicComplex) f ![true,true,false,false]=M.output (K:=AlgebraicComplex) f ![false,false,true,true] :=
    M.output_swap f true true false false
  have symB : M.output (K:=AlgebraicComplex) f ![true,false,false,true]=M.output (K:=AlgebraicComplex) f ![false,true,true,false] :=
    M.output_swap f true false false true
  have symC : ‖(M.output (K:=AlgebraicComplex) f ![true,false,true,false] : ℂ)‖=
      ‖(M.output (K:=AlgebraicComplex) f ![false,true,false,true] : ℂ)‖ := by
    change ‖P.inclusion _‖=‖P.inclusion _‖
    rw [P.output_map,P.output_map]
    exact C.cross_complement_norm (P.complex f) hf
  have hA : ‖(M.output (K:=AlgebraicComplex) f ![false,false,true,true] : ℂ)‖=
      G.rowMass (C.row (P.complex f) false false) := by
    change ‖P.inclusion _‖=_
    rw [P.output_map]
    exact C.diagonal_norm (P.complex f) hf false false
  have hB : ‖(M.output (K:=AlgebraicComplex) f ![false,true,true,false] : ℂ)‖=
      G.rowMass (C.row (P.complex f) false true) := by
    change ‖P.inclusion _‖=_
    rw [P.output_map]
    exact C.diagonal_norm (P.complex f) hf false true
  have hC : ‖(M.output (K:=AlgebraicComplex) f ![false,true,false,true] : ℂ)‖=
      ‖G.rowInner (C.row (P.complex f) false true) (C.row (P.complex f) true false)‖ := by
    change ‖P.inclusion _‖=_
    rw [P.output_map]
    exact C.cross_norm (P.complex f) hf
  have hab : ‖(M.output (K:=AlgebraicComplex) f ![false,false,true,true] : ℂ)‖<
      ‖(M.output (K:=AlgebraicComplex) f ![false,true,true,false] : ℂ)‖ := by
    rw [hA,hB]
    rw [P.correlation_prefix (P.complex f) hf] at negative
    linarith
  have hb : M.output (K:=AlgebraicComplex) f ![false,true,true,false]≠0 := by
    intro h
    simp only [h,ZeroMemClass.coe_zero,norm_zero] at hab
    exact (not_lt_of_ge (norm_nonneg _)) hab
  have ha := R.same_zero (M.output (K:=AlgebraicComplex) f) symA symB hab ht
  by_cases hc : M.output (K:=AlgebraicComplex) f ![false,true,false,true]=0
  · left
    have hd : M.output (K:=AlgebraicComplex) f ![true,false,true,false]=0 := by
      apply P.inclusion.injective
      change P.inclusion _=P.inclusion 0
      rw [map_zero]
      apply norm_eq_zero.mp
      simpa [hc] using symC
    exact isolated (M.output (K:=AlgebraicComplex) f) (by simpa only [M.denote] using M.central f he)
      ha hc hd (symA.trans ha) hb (by rwa [symB])
  · right
    apply P.free_prefix f hf
    · simpa [ha] using hA.symm
    · rw [←hB]
      exact lt_of_le_of_lt (norm_nonneg _) hab
    · have hh := R.cross_saturated (M.output (K:=AlgebraicComplex) f) symB symC hab ht hc
      rwa [hC,hB] at hh

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedSplit
