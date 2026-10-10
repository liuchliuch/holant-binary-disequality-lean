import Holant.Tractable.Conformal.MatrixSupport

/-! Exact family transport, preprocessing, and shared conformal bases. -/
namespace Holant.Tractable
noncomputable section
namespace Conformal

@[simp] theorem action_eq_zero_iff (B : InvertibleKernel) {n : ℕ}
    (f : Signature AlgebraicComplex n) : B.action f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have := congrArg B.symm.action h
    rw [InvertibleKernel.symm_action_action] at this
    simpa only [InvertibleKernel.action, Signature.coordinateAction_zero] using this
  · rintro rfl
    exact Signature.coordinateAction_zero _

@[simp] theorem familyAction_identity (F : SignatureFamily AlgebraicComplex) :
    familyAction InvertibleKernel.identity F = F := by
  ext f
  simp only [familyAction, Set.mem_image]
  constructor
  · rintro ⟨g, hg, he⟩
    simp only [InvertibleKernel.identity_action, Sigma.eta] at he
    exact he ▸ hg
  · intro hf
    exact ⟨f, hf, by simp⟩

@[simp] theorem familyAction_comp (B D : InvertibleKernel)
    (F : SignatureFamily AlgebraicComplex) :
    familyAction (B.comp D) F = familyAction B (familyAction D F) := by
  unfold familyAction
  rw [Set.image_image]
  congr 1
  funext f
  simp only [InvertibleKernel.comp_action]

@[simp] theorem familyAction_symm_action (B : InvertibleKernel)
    (F : SignatureFamily AlgebraicComplex) : familyAction B.symm (familyAction B F) = F := by
  unfold familyAction
  rw [Set.image_image]
  convert Set.image_id F using 1
  congr 1
  funext f
  simp

@[simp] theorem familyAction_action_symm (B : InvertibleKernel)
    (F : SignatureFamily AlgebraicComplex) : familyAction B (familyAction B.symm F) = F := by
  simpa only [InvertibleKernel.symm_symm] using familyAction_symm_action B.symm F

@[simp] theorem familyAction_finite_iff (B : InvertibleKernel)
    (F : SignatureFamily AlgebraicComplex) : (familyAction B F).Finite ↔ F.Finite := by
  constructor
  · intro h
    have hi := h.image (fun f : AnySignature AlgebraicComplex => (⟨f.1, B.symm.action f.2⟩ : AnySignature AlgebraicComplex))
    exact (familyAction_symm_action B F) ▸ hi
  · intro h
    exact h.image _

@[simp] theorem preprocess_familyAction (B : InvertibleKernel)
    (F : SignatureFamily AlgebraicComplex) :
    preprocess (familyAction B F) = familyAction B (preprocess F) := by
  ext f
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hn, hz⟩
    exact ⟨g, ⟨hg, hn, fun h => hz ((action_eq_zero_iff B g.2).mpr h)⟩, rfl⟩
  · rintro ⟨g, ⟨hg, hn, hz⟩, rfl⟩
    exact ⟨⟨g, hg, rfl⟩, hn, fun h => hz ((action_eq_zero_iff B g.2).mp h)⟩

theorem preprocessed_familyAction (B : InvertibleKernel)
    {F : SignatureFamily AlgebraicComplex} (hF : Preprocessed F) :
    Preprocessed (familyAction B F) := by
  rintro f ⟨g, hg, rfl⟩
  exact ⟨(hF g hg).1, fun h => (hF g hg).2 ((action_eq_zero_iff B g.2).mp h)⟩

@[simp] theorem kCoordinates_familyAction (F : SignatureFamily AlgebraicComplex) :
    kCoordinates (familyAction sourceKBasis F) = F := familyAction_symm_action _ _

theorem pullback_scale (E B : Kernel AlgebraicComplex) (c : AlgebraicComplex) :
    Kernel.pullback (fun a b => c * E a b) B =
      fun a b => c * Kernel.pullback E B a b := by
  funext a b
  simp only [Kernel.pullback, Kernel.mul_apply]
  ring

/-- Inverse transport retains the actual inverse conformal multiplier. -/
theorem pullback_inverse (E : Kernel AlgebraicComplex) (A : InvertibleKernel)
    {c : AlgebraicComplex} (hc : c ≠ 0)
    (hA : Kernel.pullback E A.matrix = fun a b => c * E a b) :
    Kernel.pullback E A.inverse = fun a b => c⁻¹ * E a b := by
  have hcancel : Kernel.pullback (Kernel.pullback E A.matrix) A.inverse = E := by
    rw [← pullback_mul, A.matrix_inverse]
    simp [Kernel.pullback]
  rw [hA, pullback_scale] at hcancel
  funext a b
  have h := congrFun (congrFun hcancel a) b
  change c * Kernel.pullback E A.inverse a b = E a b at h
  rw [← h]
  simp [hc]

/-- The single computational-coordinate action conjugate to `D` in K coordinates. -/
def kConjugate (D : InvertibleKernel) : InvertibleKernel :=
  sourceKBasis.comp (D.comp sourceKBasis.symm)

theorem kConjugate_pullback (D : InvertibleKernel) {c : AlgebraicComplex}
    (hD : Kernel.pullback Signature.disequality D.matrix =
      fun a b => c * Signature.disequality a b) :
    Kernel.pullback Signature.equality (kConjugate D).matrix =
      fun a b => c * Signature.equality a b := by
  have hK : Kernel.pullback Signature.disequality sourceKBasis.inverse =
      Signature.equality := by
    rw [← sourceKBasis_pullback, ← pullback_mul, sourceKBasis.matrix_inverse]
    simp [Kernel.pullback]
  change Kernel.pullback Signature.equality
    (Kernel.mul sourceKBasis.matrix (Kernel.mul D.matrix sourceKBasis.inverse)) = _
  rw [pullback_mul, sourceKBasis_pullback, pullback_mul, hD, pullback_scale, hK]

theorem kConjugate_familyAction (D : InvertibleKernel)
    (F : SignatureFamily AlgebraicComplex) :
    familyAction (kConjugate D) (familyAction sourceKBasis F) =
      familyAction sourceKBasis (familyAction D F) := by
  simp only [kConjugate, familyAction_comp, familyAction_symm_action]

/-- A closure hypothesis used only for the following general transport lemma;
actual affine, product, and local-affine instances are proved below. -/
def ScaleClosed (C : SignatureFamily AlgebraicComplex) : Prop :=
  ∀ n (f : Signature AlgebraicComplex n), (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ C →
    ∀ c : AlgebraicComplex, (⟨n, fun x => c * f x⟩ : AnySignature AlgebraicComplex) ∈ C

theorem affineClass_scaleClosed : ScaleClosed affineClass := by
  intro n f hf c
  exact Affine.scale hf c

theorem productClass_scaleClosed : ScaleClosed productClass := by
  intro n f hf c
  exact Product.scale hf c

theorem localAffineClass_scaleClosed : ScaleClosed localAffineClass := by
  intro n f hf c
  exact LocalAffine.scale hf c

/-- The whole family uses the one transported witness `A W`; no member gets a
separately chosen basis. The edge condition is the same actual scaled edge. -/
theorem commonTransformable_map {C F : SignatureFamily AlgebraicComplex}
    (hC : ScaleClosed C) (A : InvertibleKernel) (c : AlgebraicComplex)
    (hA : Kernel.pullback Signature.equality A.matrix =
      fun a b => c * Signature.equality a b)
    (hF : CommonTransformable C F) : CommonTransformable C (familyAction A F) := by
  obtain ⟨hfin, W, hedge, hfamily⟩ := hF
  refine ⟨hfin.image _, A.comp W, ?_, ?_⟩
  · change (⟨2, kernelSignature (Kernel.pullback Signature.equality
        (Kernel.mul A.matrix W.matrix))⟩ : AnySignature AlgebraicComplex) ∈ C
    rw [pullback_mul, hA, pullback_scale]
    exact hC 2 _ hedge c
  · rintro f ⟨g, hg, rfl⟩
    simpa only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
      InvertibleKernel.symm_action_action] using hfamily g hg

theorem commonTransformable_iff_map {C F : SignatureFamily AlgebraicComplex}
    (hC : ScaleClosed C) (A : InvertibleKernel) {c : AlgebraicComplex} (hc : c ≠ 0)
    (hA : Kernel.pullback Signature.equality A.matrix =
      fun a b => c * Signature.equality a b) :
    CommonTransformable C F ↔ CommonTransformable C (familyAction A F) := by
  constructor
  · exact commonTransformable_map hC A c hA
  · intro h
    simpa only [familyAction_symm_action] using
      commonTransformable_map hC A.symm c⁻¹ (pullback_inverse _ A hc hA) h

/-- Each of the three exact manuscript classes has conformally invariant
common transformability in transported K coordinates. -/
theorem xConformal_commonTransformable {D : InvertibleKernel} (hD : XConformal D)
    (F : SignatureFamily AlgebraicComplex) :
    (CommonTransformable affineClass (familyAction sourceKBasis F) ↔
      CommonTransformable affineClass (familyAction sourceKBasis (familyAction D F))) ∧
    (CommonTransformable productClass (familyAction sourceKBasis F) ↔
      CommonTransformable productClass (familyAction sourceKBasis (familyAction D F))) ∧
    (CommonTransformable localAffineClass (familyAction sourceKBasis F) ↔
      CommonTransformable localAffineClass (familyAction sourceKBasis (familyAction D F))) := by
  obtain ⟨c, hc, he⟩ := hD
  have hA := kConjugate_pullback D he
  constructor
  · simpa only [kConjugate_familyAction] using
      commonTransformable_iff_map (F := familyAction sourceKBasis F) affineClass_scaleClosed (kConjugate D) hc hA
  constructor
  · simpa only [kConjugate_familyAction] using
      commonTransformable_iff_map (F := familyAction sourceKBasis F) productClass_scaleClosed (kConjugate D) hc hA
  · simpa only [kConjugate_familyAction] using
      commonTransformable_iff_map (F := familyAction sourceKBasis F) localAffineClass_scaleClosed (kConjugate D) hc hA

end Conformal

/-- The inverse of a genuine conformal kernel is genuinely conformal. -/
theorem XConformal.symm {D : InvertibleKernel} (hD : XConformal D) : XConformal D.symm := by
  obtain ⟨c, hc, he⟩ := hD
  exact ⟨c⁻¹, inv_ne_zero hc, Conformal.pullback_inverse _ D hc he⟩

end
end Holant.Tractable
