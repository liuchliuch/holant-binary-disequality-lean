import Holant.Tractable.Conformal.Shape

/-! Exact tensor factor arity and common matching orientation transport. -/
namespace Holant.Tractable
noncomputable section
namespace Conformal

theorem sourceTensorClosure_map {C E : (n : ℕ) → Signature AlgebraicComplex n → Prop}
    (A : InvertibleKernel)
    (hmap : ∀ n f, C n f → E n (A.action f))
    {n : ℕ} {f : Signature AlgebraicComplex n} (hf : SourceTensorClosure C f) :
    SourceTensorClosure E (A.action f) := by
  rcases hf with rfl | hf
  · exact Or.inl (Signature.coordinateAction_zero _)
  · exact Or.inr (hf.map_action A.matrix hmap)

theorem arityTwo_map (A : InvertibleKernel) {F : SignatureFamily AlgebraicComplex}
    (hF : ArityTwoAlternative F) : ArityTwoAlternative (familyAction A F) := by
  rintro f ⟨g, hg, rfl⟩
  exact sourceTensorClosure_map A (fun _ _ h => h) (hF g hg)

theorem arityTwo_iff_map (A : InvertibleKernel) (F : SignatureFamily AlgebraicComplex) :
    ArityTwoAlternative F ↔ ArityTwoAlternative (familyAction A F) := by
  constructor
  · exact arityTwo_map A
  · intro h
    simpa only [familyAction_symm_action] using arityTwo_map A.symm h

def orientationKernel (opposite : Bool) : Kernel AlgebraicComplex :=
  if opposite then Signature.disequality else Signature.equality

theorem matchingImage_iff (opposite : Bool) {n : ℕ} (f : Signature AlgebraicComplex n) :
    matchingImage opposite n f ↔ ∃ g : Signature AlgebraicComplex n, AtMostOneSupport g ∧
      Signature.coordinateAction (fun _ => Kernel.mul KMatrix (orientationKernel opposite)) g = f := by
  cases opposite <;> simp [matchingImage, orientationKernel]

theorem kConjugate_mul_K (D : InvertibleKernel) :
    Kernel.mul (kConjugate D).matrix KMatrix = Kernel.mul KMatrix D.matrix := by
  change Kernel.mul (Kernel.mul sourceKBasis.matrix
    (Kernel.mul D.matrix sourceKBasis.inverse)) sourceKBasis.matrix =
      Kernel.mul sourceKBasis.matrix D.matrix
  rw [Kernel.mul_assoc, Kernel.mul_assoc, sourceKBasis.inverse_matrix, Kernel.mul_equality]

/-- Move the row-diagonal multiplier past the globally chosen complement. -/
theorem shape_orientation_matrix {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t) (old : Bool) :
    Kernel.mul D.matrix (orientationKernel old) =
      Kernel.mul (orientationKernel (Bool.xor opposite old))
        (diagonalKernel (if Bool.xor opposite old then t else s)
          (if Bool.xor opposite old then s else t)) := by
  rw [hD]
  funext a b
  cases opposite <;> cases old <;> cases a <;> cases b <;>
    simp [orientationKernel, Kernel.mul_apply, diagonalKernel,
      Signature.equality, Signature.disequality]

theorem matchingImage_shape {D : InvertibleKernel} {opposite : Bool}
    {s t : AlgebraicComplex} (hD : HasShape D opposite s t) (old : Bool)
    {n : ℕ} {f : Signature AlgebraicComplex n} (hf : matchingImage old n f) :
    matchingImage (Bool.xor opposite old) n ((kConjugate D).action f) := by
  rw [matchingImage_iff] at hf ⊢
  obtain ⟨g, hg, rfl⟩ := hf
  let L := diagonalKernel (if Bool.xor opposite old then t else s)
    (if Bool.xor opposite old then s else t)
  refine ⟨Signature.coordinateAction (fun _ => L) g, ?_, ?_⟩
  · intro x hx
    rw [coordinateAction_diagonal]
    simp only [hg x hx, mul_zero]
  · change Signature.coordinateAction _ (Signature.coordinateAction _ g) =
      Signature.coordinateAction _ (Signature.coordinateAction _ g)
    rw [Signature.coordinateAction_comp, Signature.coordinateAction_comp]
    congr 1
    funext j
    rw [← Kernel.mul_assoc (kConjugate D).matrix, kConjugate_mul_K]
    rw [Kernel.mul_assoc KMatrix D.matrix, shape_orientation_matrix hD, Kernel.mul_assoc]

theorem matching_map {D : InvertibleKernel} (hD : XConformal D)
    {F : SignatureFamily AlgebraicComplex} (hF : MatchingAlternative F) :
    MatchingAlternative (familyAction (kConjugate D) F) := by
  obtain ⟨opposite, s, t, hs, ht, hshape⟩ := hasShape_of_xConformal hD
  have transport (old : Bool) (h : ∀ f ∈ F, SourceTensorClosure (matchingImage old) f.2) :
      ∀ f ∈ familyAction (kConjugate D) F,
        SourceTensorClosure (matchingImage (Bool.xor opposite old)) f.2 := by
    rintro f ⟨g, hg, rfl⟩
    exact sourceTensorClosure_map (kConjugate D)
      (fun _ _ hh => matchingImage_shape hshape old hh) (h g hg)
  cases opposite
  · rcases hF with hF | hF
    · exact Or.inl (transport false hF)
    · exact Or.inr (transport true hF)
  · rcases hF with hF | hF
    · exact Or.inr (transport false hF)
    · exact Or.inl (transport true hF)

end Conformal
end
end Holant.Tractable
