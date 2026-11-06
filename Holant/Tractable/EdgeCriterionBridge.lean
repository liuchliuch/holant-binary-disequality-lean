import Holant.Tractable.SymmetricBinaryPullback
import Holant.Tractable.STOC2027
import Holant.Tractable.Anchor.MatrixActions

/-! The edge-model criterion identity in the November 2026 manuscript.
All class closures below are derived for the concrete affine, product and
local-affine classes. No tractability or classification theorem is imported. -/
namespace Holant.Tractable
noncomputable section
namespace EdgeCriterionBridge
open SymmetricBinaryPullback Conformal

/-- Uniqueness of the actual two-sided inverse. -/
theorem inverse_eq (E : InvertibleKernel) :
    E.inverse = (invertibleOfDeterminant E.matrix (determinant_ne_zero E)).inverse := by
  let D := invertibleOfDeterminant E.matrix (determinant_ne_zero E)
  calc
    E.inverse = Kernel.mul E.inverse Signature.equality := (Kernel.mul_equality _).symm
    _ = Kernel.mul E.inverse (Kernel.mul E.matrix D.inverse) := by
      have hd : Kernel.mul E.matrix D.inverse = Signature.equality := D.matrix_inverse
      rw [hd]
    _ = D.inverse := by rw [← Kernel.mul_assoc, E.inverse_matrix, Kernel.equality_mul]

/-- Transpose retains the certified inverse. -/
def transpose (E : InvertibleKernel) : InvertibleKernel where
  matrix := Kernel.transpose E.matrix
  inverse := Kernel.transpose E.inverse
  matrix_inverse := by rw [← Kernel.transpose_mul, E.inverse_matrix]; funext a b; cases a <;> cases b <;> rfl
  inverse_matrix := by rw [← Kernel.transpose_mul, E.matrix_inverse]; funext a b; cases a <;> cases b <;> rfl

/-- An inverse of a symmetric matrix is symmetric. -/
theorem inverse_symmetric (E : InvertibleKernel)
    (hE : Kernel.transpose E.matrix = E.matrix) : Kernel.transpose E.inverse = E.inverse := by
  have h : E.matrix true false = E.matrix false true := congrFun (congrFun hE false) true
  rw [inverse_eq]
  funext a b
  cases a <;> cases b <;> simp [invertibleOfDeterminant, adjugate, Kernel.transpose, h]

private theorem affine_sign :
    Affine (fun x : Fin 2 → Bool =>
      (if x 0 then (-1 : AlgebraicComplex) else 1) * (if x 1 then -1 else 1)) := by
  let Q : QuadraticPhase 2 := ⟨0, fun _ => 2, fun _ _ => 0, fun _ _ _ => Or.inl rfl⟩
  convert affine_formula 1 (AffineSystem.unconstrained 2) Q using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    norm_num [affineFormula, Q, QuadraticPhase.eval, Fin.sum_univ_two, bitValue, h0, h1,
      fourthRootPhase, imaginaryUnit_sq]
  all_goals norm_num [show (2 : ZMod 4).val = 2 from rfl, show (4 : ZMod 4).val = 0 from rfl, imaginaryUnit_sq]

/-- Symmetric affine binaries remain affine under matrix inversion. -/
theorem affine_inverse (E : InvertibleKernel) (hE : Affine (kernelSignature E.matrix))
    (hs : Kernel.transpose E.matrix = E.matrix) : Affine (kernelSignature E.inverse) := by
  have hm : TwoTranslate.IsAffineMap (fun x : Fin 2 → Bool => fun j => !(x j)) := by
    intro x y
    funext j
    cases hx : x j <;> cases hy : y j <;> simp [AffinePhase.xor, AffinePhase.origin, hx, hy]
  have h := ((hE.precompose _ hm).mul affine_sign).scale (determinant E.matrix)⁻¹
  have he : E.matrix true false = E.matrix false true := congrFun (congrFun hs false) true
  convert h using 1
  rw [inverse_eq]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature, invertibleOfDeterminant, adjugate, h0, h1, div_eq_mul_inv, he,
      mul_comm]

/-- Product binaries retain their diagonal/antidiagonal support under inversion. -/
theorem product_inverse (E : InvertibleKernel) (hE : Product (kernelSignature E.matrix)) :
    Product (kernelSignature E.inverse) := by
  apply product_of_monomial
  rw [inverse_eq]
  rcases product_monomial hE (determinant_ne_zero E) with h | h
  · left; simp [invertibleOfDeterminant, adjugate, h.1, h.2]
  · right; simp [invertibleOfDeterminant, adjugate, h.1, h.2]

/-- The concrete diagonal fourth-root normal form proves local-affine inversion. -/
theorem localAffine_inverse (E : InvertibleKernel) (hE : LocalAffine (kernelSignature E.matrix))
    (hs : Kernel.transpose E.matrix = E.matrix) : LocalAffine (kernelSignature E.inverse) := by
  obtain ⟨he, ha, hc, hp⟩ := localAffine_diagonal_characterization E hE hs
  have hz := localAffine_offdiagonal_zero hE hs
  have hi : E.inverse = diagonal (E.matrix false false)⁻¹ (E.matrix true true)⁻¹ := by
    rw [inverse_eq]
    funext a b
    cases a <;> cases b <;>
      simp [invertibleOfDeterminant, adjugate, determinant, hz.1, hz.2, diagonal, hc,
        mul_inv_rev, div_eq_mul_inv]
    field_simp
  rw [hi]
  exact localAffine_diagonal _ _ (inv_ne_zero ha) (by simp only [inv_pow, hp])

theorem class_inverse (C : SignatureFamily AlgebraicComplex)
    (hC : C ∈ ({affineClass, productClass, localAffineClass} : Set (SignatureFamily AlgebraicComplex)))
    (E : InvertibleKernel) (hE : (⟨2, kernelSignature E.matrix⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hs : Kernel.transpose E.matrix = E.matrix) :
    (⟨2, kernelSignature E.inverse⟩ : AnySignature AlgebraicComplex) ∈ C := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with rfl | rfl | rfl
  · exact affine_inverse E hE hs
  · exact product_inverse E hE
  · exact localAffine_inverse E hE hs

/-- The edge pullback, packaged with its genuine inverse. -/
def edge (E M : InvertibleKernel) : InvertibleKernel :=
  (transpose M).comp (E.comp M)

/-- The image of a binary vertex under the common inverse basis. -/
def vertex (E M : InvertibleKernel) : InvertibleKernel :=
  (M.symm.comp E).comp (transpose M.symm)

@[simp] theorem edge_matrix (E M : InvertibleKernel) :
    (edge E M).matrix = Kernel.pullback E.matrix M.matrix := by
  simp only [edge, transpose, InvertibleKernel.comp, Kernel.pullback, Kernel.mul_assoc]

@[simp] theorem vertex_matrix (E M : InvertibleKernel) :
    kernelSignature (vertex E M).matrix = M.symm.action (kernelSignature E.matrix) := by
  exact (coordinateAction_kernelSignature _ _).symm

theorem edge_symmetric (E M : InvertibleKernel)
    (hs : Kernel.transpose E.matrix = E.matrix) :
    Kernel.transpose (edge E M).matrix = (edge E M).matrix := by
  simp only [edge_matrix, Kernel.pullback, Kernel.transpose_mul, Kernel.transpose_transpose, hs,
    Kernel.mul_assoc]

theorem vertex_symmetric (E M : InvertibleKernel)
    (hs : Kernel.transpose E.matrix = E.matrix) :
    Kernel.transpose (vertex E M).matrix = (vertex E M).matrix := by
  simp only [vertex, InvertibleKernel.comp, InvertibleKernel.symm, transpose,
    Kernel.transpose_mul, Kernel.transpose_transpose, hs, Kernel.mul_assoc]

private theorem edge_vertex_edge (E F M : InvertibleKernel) :
    Kernel.mul (Kernel.mul (edge E M).matrix (vertex F M).matrix) (edge E M).matrix =
      Kernel.pullback (Kernel.mul (Kernel.mul E.matrix F.matrix) E.matrix) M.matrix := by
  have ht : Kernel.mul (Kernel.transpose M.inverse) (Kernel.transpose M.matrix) =
      Signature.equality := by rw [← Kernel.transpose_mul, M.matrix_inverse, Kernel.transpose_equality]
  simp only [edge, vertex, InvertibleKernel.comp, InvertibleKernel.symm, transpose,
    Kernel.pullback, Kernel.mul_assoc]
  rw [← Kernel.mul_assoc M.matrix M.inverse, M.matrix_inverse, Kernel.equality_mul,
    ← Kernel.mul_assoc (Kernel.transpose M.inverse) (Kernel.transpose M.matrix), ht,
    Kernel.equality_mul]

private theorem vertex_edge_vertex (E F M : InvertibleKernel) :
    Kernel.mul (Kernel.mul (vertex E M).matrix (edge F M).matrix) (vertex E M).matrix =
      (vertex ((E.comp F).comp E) M).matrix := by
  have ht : Kernel.mul (Kernel.transpose M.inverse) (Kernel.transpose M.matrix) =
      Signature.equality := by rw [← Kernel.transpose_mul, M.matrix_inverse, Kernel.transpose_equality]
  simp only [edge, vertex, InvertibleKernel.comp, InvertibleKernel.symm, transpose,
    Kernel.mul_assoc]
  rw [← Kernel.mul_assoc (Kernel.transpose M.inverse) (Kernel.transpose M.matrix), ht,
    Kernel.equality_mul, ← Kernel.mul_assoc M.matrix M.inverse, M.matrix_inverse,
    Kernel.equality_mul]

private theorem ordinary_edge_inverse (M : InvertibleKernel) :
    (edge InvertibleKernel.identity M).inverse = (vertex InvertibleKernel.identity M).matrix := by
  simp only [edge, vertex, InvertibleKernel.comp, InvertibleKernel.symm, transpose,
    InvertibleKernel.identity, Kernel.equality_mul, Kernel.mul_equality]

/-- The same basis works for the entire family in either edge model. -/
theorem common_basis_edge_bridge (C : SignatureFamily AlgebraicComplex)
    (hC : C ∈ ({affineClass, productClass, localAffineClass} : Set (SignatureFamily AlgebraicComplex)))
    (F : SignatureFamily AlgebraicComplex) :
    CommonTransformable C (F ∪ {(⟨2, kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)}) ↔
    CommonKPresentationInKCoordinates C
      (F ∪ {(⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)}) := by
  constructor
  · rintro ⟨hfin, M, hedge, hfamily⟩
    have hx : (⟨2, kernelSignature (vertex bitFlipBasis M).matrix⟩ : AnySignature AlgebraicComplex) ∈ C := by
      rw [vertex_matrix]
      exact hfamily _ (Or.inr rfl)
    have he : (⟨2, kernelSignature (edge InvertibleKernel.identity M).matrix⟩ : AnySignature AlgebraicComplex) ∈ C := by
      simpa only [edge_matrix, InvertibleKernel.identity, bitFlipBasis] using hedge
    have hi := class_inverse C hC (edge InvertibleKernel.identity M) he
      (edge_symmetric _ _ Kernel.transpose_equality)
    rw [ordinary_edge_inverse, vertex_matrix] at hi
    have hn := symmetric_binary_pullback C hC (edge InvertibleKernel.identity M)
      (vertex bitFlipBasis M) he hx
      (edge_symmetric _ _ Kernel.transpose_equality)
      (vertex_symmetric _ _ Kernel.transpose_disequality)
    rw [edge_vertex_edge] at hn
    simp only [InvertibleKernel.identity, Kernel.equality_mul, Kernel.mul_equality] at hn
    refine ⟨(hfin.subset Set.subset_union_left).union (Set.finite_singleton _), M, hn, ?_⟩
    intro f hf
    rcases hf with hf | hf
    · exact hfamily f (Or.inl hf)
    · rcases hf with rfl
      exact hi
  · rintro ⟨hfin, M, hedge, hfamily⟩
    have hi : (⟨2, kernelSignature (vertex InvertibleKernel.identity M).matrix⟩ : AnySignature AlgebraicComplex) ∈ C := by
      rw [vertex_matrix]
      exact hfamily _ (Or.inr rfl)
    have he : (⟨2, kernelSignature (edge bitFlipBasis M).matrix⟩ : AnySignature AlgebraicComplex) ∈ C := by
      simpa only [edge_matrix, InvertibleKernel.identity, bitFlipBasis] using hedge
    have ho := symmetric_binary_pullback C hC (edge bitFlipBasis M)
      (vertex InvertibleKernel.identity M) he hi
      (edge_symmetric _ _ Kernel.transpose_disequality)
      (vertex_symmetric _ _ Kernel.transpose_equality)
    rw [edge_vertex_edge] at ho
    simp only [bitFlipBasis, InvertibleKernel.identity, Kernel.mul_equality,
      Kernel.disequality_mul_disequality] at ho
    have hx := symmetric_binary_pullback C hC (vertex InvertibleKernel.identity M)
      (edge bitFlipBasis M) hi he
      (vertex_symmetric _ _ Kernel.transpose_equality)
      (edge_symmetric _ _ Kernel.transpose_disequality)
    rw [vertex_edge_vertex, vertex_matrix] at hx
    simp only [InvertibleKernel.comp, InvertibleKernel.identity, Kernel.equality_mul,
      Kernel.mul_equality] at hx
    refine ⟨(hfin.subset Set.subset_union_left).union (Set.finite_singleton _), M, ho, ?_⟩
    intro f hf
    rcases hf with hf | hf
    · exact hfamily f (Or.inl hf)
    · rcases hf with rfl
      exact hx


end EdgeCriterionBridge
end
end Holant.Tractable
