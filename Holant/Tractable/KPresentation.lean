import Holant.Tractable.CommonTransform

/-! The source matrix `K = (1/√2) [[1,1],[i,-i]]` and exact source-coordinate
common K-presentation. Its inverse and `KᵀK=X` are checked identities, without
conjugation. The equivalence of the two common-basis predicates is proved below. -/
namespace Holant.Tractable
noncomputable section
/-- The fixed matrix from the manuscript, in Boolean row/column order. -/
def KMatrix : Kernel AlgebraicComplex := fun a b =>
  (if a then (if b then -imaginaryUnit else imaginaryUnit) else 1) / sqrtTwo
def KInverse : Kernel AlgebraicComplex := fun a b =>
  (if b then (if a then imaginaryUnit else -imaginaryUnit) else 1) / sqrtTwo
theorem KMatrix_mul_inverse : Kernel.mul KMatrix KInverse = Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul_apply, KMatrix, KInverse, Signature.equality,
      div_mul_div_comm, ← pow_two, imaginaryUnit_sq, sqrtTwo_sq] <;> ring
theorem KInverse_mul_matrix : Kernel.mul KInverse KMatrix = Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul_apply, KMatrix, KInverse, Signature.equality,
      div_mul_div_comm, ← pow_two, imaginaryUnit_sq, sqrtTwo_sq] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq, inv_pow, sqrtTwo_sq]
theorem KMatrix_transpose_mul : Kernel.mul (Kernel.transpose KMatrix) KMatrix = Signature.disequality := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul_apply, Kernel.transpose, KMatrix, Signature.disequality,
      div_mul_div_comm, ← pow_two, imaginaryUnit_sq, sqrtTwo_sq] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq, inv_pow, sqrtTwo_sq]
/-- The exact source matrix together with its certified two-sided inverse. -/
def sourceKBasis : InvertibleKernel :=
  ⟨KMatrix, KInverse, KMatrix_mul_inverse, KInverse_mul_matrix⟩

@[simp] theorem sourceKBasis_pullback :
    Kernel.pullback Signature.equality sourceKBasis.matrix = Signature.disequality := by
  rw [Kernel.pullback_equality]
  exact KMatrix_transpose_mul

/-- The manuscript's `PresK(F; C)` in the original computational coordinates.
Both the fixed `K⁻¹` and the common `U⁻¹` act on each entire signature; a single
`U` also transforms the disequality edge. -/
def CommonKPresentation (C F : SignatureFamily AlgebraicComplex) : Prop :=
  F.Finite ∧ ∃ U : InvertibleKernel,
    (⟨2, kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ C ∧
    ∀ f ∈ F, (⟨f.1, U.symm.action (sourceKBasis.symm.action f.2)⟩ :
      AnySignature AlgebraicComplex) ∈ C

/-- Bilinear edge pullbacks compose in the same order as the column basis matrices. -/
theorem pullback_mul (E A B : Kernel AlgebraicComplex) :
    Kernel.pullback E (Kernel.mul A B) = Kernel.pullback (Kernel.pullback E A) B := by
  simp only [Kernel.pullback, Kernel.transpose_mul, Kernel.mul_assoc]

/-- The source's change from one shared computational basis to one shared K-basis.
No per-signature choice and no closure or tractability assumption is used. -/
theorem commonTransformable_iff_commonKPresentation
    (C F : SignatureFamily AlgebraicComplex) :
    CommonTransformable C F ↔ CommonKPresentation C F := by
  constructor
  · rintro ⟨hfin, B, hedge, hfamily⟩
    refine ⟨hfin, sourceKBasis.symm.comp B, ?_, ?_⟩
    · have he : Kernel.pullback Signature.disequality
          (sourceKBasis.symm.comp B).matrix =
          Kernel.pullback Signature.equality B.matrix := by
        rw [← sourceKBasis_pullback, ← pullback_mul]
        change Kernel.pullback Signature.equality
          (Kernel.mul sourceKBasis.matrix (Kernel.mul sourceKBasis.inverse B.matrix)) = _
        rw [← Kernel.mul_assoc, sourceKBasis.matrix_inverse, Kernel.equality_mul]
      simpa only [he] using hedge
    · intro f hf
      simpa only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
        InvertibleKernel.symm_symm, InvertibleKernel.action_symm_action] using hfamily f hf
  · rintro ⟨hfin, U, hedge, hfamily⟩
    refine ⟨hfin, sourceKBasis.comp U, ?_, ?_⟩
    · simpa only [InvertibleKernel.comp, pullback_mul, sourceKBasis_pullback] using hedge
    · intro f hf
      simpa only [InvertibleKernel.comp_symm, InvertibleKernel.comp_action] using hfamily f hf

end
end Holant.Tractable
