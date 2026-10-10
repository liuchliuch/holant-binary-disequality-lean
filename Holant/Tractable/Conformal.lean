import Holant.Tractable.Conformal.EOAlternatives
import Holant.Tractable.Conformal.TensorAlternatives

/-!
# GO(X)-invariance of the seven-clause structural criterion

Authoritative `paper1.tex`, rewritten 2026-09-27, Lemma 2.22,
`lem:GOX-tract-invariance` (lines 3272–3306).

`XConformal` is the actual nonzero-multiplier equation `Dᵀ X D = c X` for
an invertible Boolean kernel. Entry comparison proves diagonal/antidiagonal
classification. Tensor action has its exact wordwise coefficient, which is
constant on every fixed Hamming layer. EO transport preserves the one shared
A/P class and either retains or reverses the one shared sign and every oriented
pair. Single-layer completions retain their literal original-ports-first order.
The matching alternative retains or exchanges its single global orientation.
The three common-basis clauses use the one conjugated witness `K D K⁻¹ W`
and the actual nonzero edge scale, with proved A/P/L scalar closure.

The public theorem first performs the exact zero/nullary preprocessing. No
algorithm, complexity bound, recognition routine, or hardness claim is imported
or inferred from this structural result.
-/

namespace Holant.Tractable
noncomputable section
namespace Conformal

/-- Forward transport of all seven literal alternatives on a finite family. -/
theorem tractCore_map {D : InvertibleKernel} (hD : XConformal D)
    {G : SignatureFamily AlgebraicComplex} (hfin : G.Finite)
    (hG : TractCore (familyAction sourceKBasis G)) :
    TractCore (familyAction sourceKBasis (familyAction D G)) := by
  rcases hG with h | h | h | h | h | h | h
  · exact Or.inl (oneSided_map hD hfin h)
  · exact Or.inr (Or.inl (singleWeight_map hD hfin h))
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    simpa only [kConjugate_familyAction] using arityTwo_map (kConjugate D) h
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    simpa only [kConjugate_familyAction] using matching_map hD h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((xConformal_commonTransformable hD G).1.mp h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((xConformal_commonTransformable hD G).2.1.mp h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((xConformal_commonTransformable hD G).2.2.mp h))))))

/-- Forward public transport, including the prescribed deletion step. -/
theorem tract_map {D : InvertibleKernel} (hD : XConformal D)
    {G : SignatureFamily AlgebraicComplex} (hG : Tract (familyAction sourceKBasis G)) :
    Tract (familyAction sourceKBasis (familyAction D G)) := by
  have hpre : (familyAction sourceKBasis (preprocess G)).Finite ∧
      TractCore (familyAction sourceKBasis (preprocess G)) := by
    simpa only [Tract, preprocess_familyAction] using hG
  have hfin : (preprocess G).Finite := (familyAction_finite_iff _ _).mp hpre.1
  unfold Tract
  simp only [preprocess_familyAction]
  exact ⟨(hfin.image _).image _, tractCore_map hD hfin hpre.2⟩

end Conformal

/-- Strong public form: preprocessing makes the equivalence valid for arbitrary
input families; each side itself requires its retained family to be finite. -/
theorem xConformal_tract_iff {D : InvertibleKernel} (hD : XConformal D)
    (G : SignatureFamily AlgebraicComplex) :
    Tract (familyAction sourceKBasis G) ↔
      Tract (familyAction sourceKBasis (familyAction D G)) := by
  constructor
  · exact Conformal.tract_map hD
  · intro h
    simpa only [Conformal.familyAction_symm_action] using Conformal.tract_map hD.symm h

/-- The literal source lemma for a finite, preprocessed signature family and an
actual invertible `GO(X)` kernel. The stronger theorem also checks preprocessing. -/
theorem goX_tract_invariance (G : SignatureFamily AlgebraicComplex)
    (_hfinite : G.Finite) (_hpreprocessed : Preprocessed G)
    (D : InvertibleKernel) (hD : XConformal D) :
    Tract (familyAction sourceKBasis G) ↔
      Tract (familyAction sourceKBasis (familyAction D G)) := xConformal_tract_iff hD G

end
end Holant.Tractable
