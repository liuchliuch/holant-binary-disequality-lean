import Holant.Tractable.EdgeCriterionBridge

/-! The reduced-criterion edge bridge, including zero/nullary preprocessing.
Its tensor-arity branch uses literal one-factor decompositions of the added
binaries. The transformability branches use one common basis for the edge and
the complete original family. -/
namespace Holant.Tractable
noncomputable section
namespace ReducedEdgeBridge

private def binaryDecomposition (q : Signature AlgebraicComplex 2) :
    TensorDecomposition AlgebraicComplex 2 where
  count := 1
  arity := fun _ => 2
  factor := fun _ => q
  ports :=
    { toFun := fun x => x.2
      invFun := fun j => ⟨0, j⟩
      left_inv := by
        rintro ⟨i, j⟩
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      right_inv := fun _ => rfl }
  scale := 1

theorem binary_arityTwo (q : Signature AlgebraicComplex 2) :
    SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) q := by
  refine Or.inr ⟨binaryDecomposition q, fun _ => Or.inr rfl, ?_⟩
  funext x
  change (1 : AlgebraicComplex) * (∏ _i : Fin 1, q x) = q x
  simp

theorem arityTwo_adjoin_iff (F : SignatureFamily AlgebraicComplex)
    (q : Signature AlgebraicComplex 2) :
    ArityTwoAlternative (F ∪ {(⟨2, q⟩ : AnySignature AlgebraicComplex)}) ↔
      ArityTwoAlternative F := by
  constructor
  · intro h f hf
    exact h f (Or.inl hf)
  · intro h f hf
    rcases hf with hf | hf
    · exact h f hf
    · rcases hf with rfl
      exact binary_arityTwo q

theorem preprocess_adjoin (F : SignatureFamily AlgebraicComplex)
    (q : Signature AlgebraicComplex 2) (hq : q ≠ 0) :
    preprocess (F ∪ {(⟨2, q⟩ : AnySignature AlgebraicComplex)}) =
      preprocess F ∪ {(⟨2, q⟩ : AnySignature AlgebraicComplex)} := by
  ext f
  constructor
  · rintro ⟨hf | hf, hpos, hnz⟩
    · exact Or.inl ⟨hf, hpos, hnz⟩
    · exact Or.inr hf
  · rintro (hf | hf)
    · exact ⟨Or.inl hf.1, hf.2⟩
    · rcases hf with rfl
      exact ⟨Or.inr rfl, Nat.zero_lt_succ 1, hq⟩

theorem equality_ne_zero :
    kernelSignature (Signature.equality : Kernel AlgebraicComplex) ≠ 0 := by
  intro h
  have he := congrFun h (fun _ => false)
  norm_num [kernelSignature, Signature.equality] at he

theorem disequality_ne_zero :
    kernelSignature (Signature.disequality : Kernel AlgebraicComplex) ≠ 0 := by
  intro h
  have he := congrFun h ![false, true]
  norm_num [kernelSignature, Signature.disequality] at he

/-- The four alternatives retain their meaning under the actual edge swap. -/
theorem core_edge_bridge (F : SignatureFamily AlgebraicComplex) :
    TractXCore (F ∪ {(⟨2, kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)}) ↔
      ReTractXCore (F ∪ {(⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)}) := by
  unfold TractXCore ReTractXCore
  rw [arityTwo_adjoin_iff, arityTwo_adjoin_iff,
    EdgeCriterionBridge.common_basis_edge_bridge affineClass (by simp),
    EdgeCriterionBridge.common_basis_edge_bridge productClass (by simp),
    EdgeCriterionBridge.common_basis_edge_bridge localAffineClass (by simp)]

end ReducedEdgeBridge

/-- The literal ordinary-edge and native disequality-edge criteria coincide,
with the corresponding binary vertex adjoined in each model. -/
theorem reTract_edge_bridge (F : SignatureFamily AlgebraicComplex) :
    ReTract (F ∪ {(⟨2, kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)}) ↔
      ReTractX (F ∪ {(⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)}) := by
  unfold ReTract TractX ReTractX
  rw [ReducedEdgeBridge.preprocess_adjoin _ _ ReducedEdgeBridge.disequality_ne_zero,
    ReducedEdgeBridge.preprocess_adjoin _ _ ReducedEdgeBridge.equality_ne_zero,
    ReducedEdgeBridge.core_edge_bridge]
  simp only [Set.finite_union, Set.finite_singleton, and_true]

/-- Exact bridge from the current direct criterion to the previously proved
`K(F union {I})` criterion. No complexity conclusion is used to prove it. -/
theorem tractX_edge_bridge (F : SignatureFamily AlgebraicComplex) :
    TractX (F ∪ {(⟨2, kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)}) ↔
      TractX (familyAction sourceKBasis
        (F ∪ {(⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)})) :=
  (reTract_edge_bridge F).trans (reTractX_iff_reTract_K _)

end
end Holant.Tractable
