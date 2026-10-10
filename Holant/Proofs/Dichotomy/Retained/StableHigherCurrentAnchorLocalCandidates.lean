import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorLocalBasis

/-! The pinned local-affine common basis has sixteen explicit normalized
matrix candidates: eight eighth-root ratios and two orientations. The actual
shared nonzero scale is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorLocalCandidates
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
namespace L
export StableHigherCurrentAnchorLocalBasis (pin common_basis_normal_form)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option Elab.async false

theorem eighth_root_code (t : AlgebraicComplex) (ht : t^8=1) :
    ∃q : Fin 8,zetaEight^q.val=t := by
  have hfour : (t^4)^2=1 := by simpa only [←pow_mul] using ht
  rcases sq_eq_one_iff.mp hfour with hfour|hfour
  · obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hfour
    refine ⟨⟨2*q.val,by have := q.val_lt; omega⟩,?_⟩
    change zetaEight^(2*q.val)=t
    rw [pow_mul,zetaEight_sq]
    exact hq
  · have hdiv : (t/zetaEight)^4=1 := by
      rw [div_pow,hfour,zetaEight_pow_four]
      norm_num
    obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hdiv
    refine ⟨⟨2*q.val+1,by have := q.val_lt; omega⟩,?_⟩
    change zetaEight^(2*q.val+1)=t
    rw [pow_add,pow_mul,zetaEight_sq,pow_one]
    change fourthRootPhase q*zetaEight=t
    rw [hq,div_mul_cancel₀ _ zetaEight_ne_zero]

def candidate (opposite : Bool) (q : Fin 8) : Kernel AlgebraicComplex :=
  if opposite then antidiagonal 1 (zetaEight^q.val) else diagonal 1 (zetaEight^q.val)

/-- The finite orientation/phase choice applies to the same common basis of
all vertices and the ordinary edge; it never selects a per-row basis. -/
theorem common_basis_candidates {H : SignatureFamily AlgebraicComplex} (B : InvertibleKernel)
    (h0 : (⟨1,L.pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,L.pin true⟩ : AnySignature AlgebraicComplex)∈H)
    (hB : IsCommonBasis localAffineClass H B) :
    ∃c : AlgebraicComplex,c≠0 ∧ ∃opposite : Bool,∃q : Fin 8,
      B.matrix=fun a b=>c*candidate opposite q a b := by
  obtain ⟨c,d,hc,_,he,hm⟩ := L.common_basis_normal_form B h0 h1 hB
  have ht : (d/c)^8=1 := by
    rw [div_pow,←he,div_self (pow_ne_zero 8 hc)]
  obtain ⟨q,hq⟩ := eighth_root_code (d/c) ht
  have hd : d=c*zetaEight^q.val := by rw [hq]; field_simp
  refine ⟨c,hc,?_⟩
  rcases hm with hm|hm
  · refine ⟨false,q,?_⟩
    rw [hm,hd]
    funext a b
    cases a <;> cases b <;> simp [candidate,diagonal]
  · refine ⟨true,q,?_⟩
    rw [hm,hd]
    funext a b
    cases a <;> cases b <;> simp [candidate,antidiagonal]

theorem common_transformable_candidates {H : SignatureFamily AlgebraicComplex}
    (h0 : (⟨1,L.pin false⟩ : AnySignature AlgebraicComplex)∈H)
    (h1 : (⟨1,L.pin true⟩ : AnySignature AlgebraicComplex)∈H)
    (h : CommonTransformable localAffineClass H) :
    ∃B : InvertibleKernel,IsCommonBasis localAffineClass H B ∧
      ∃c : AlgebraicComplex,c≠0 ∧ ∃opposite : Bool,∃q : Fin 8,
        B.matrix=fun a b=>c*candidate opposite q a b := by
  obtain ⟨_,B,hB⟩ := h
  exact ⟨B,hB,common_basis_candidates B h0 h1 hB⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorLocalCandidates
