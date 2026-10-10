import Holant.Tractable.SymmetricBinaryPullback.Product
import Holant.Tractable.SymmetricBinaryPullback.LocalAffine

/-!
# Symmetric binary pullback: full source Lemma 6.28

Authoritative source: `paper1-rewritten-2026-09-27/paper1.tex`, lines 8000–8024,
`lem:symmetric-binary-pullback`. The class parameter ranges over the existing
literal signature families `affineClass`, `productClass`, and `localAffineClass`.
The two binary inputs carry the existing genuine two-sided kernel inverse
witnesses, proved equivalent to nonzero literal determinants. A determinant-facing
version constructs those inverse witnesses. Symmetry is ordinary transpose, and the conclusion is actual matrix
multiplication `EFE`, including both internal Boolean sums.

The affine route derives composition from verified Boolean substitution,
pointwise multiplication, and summation. The product route inducts over the
actual factor list: diagonal support, antidiagonal support, or determinant zero;
nonsingularity removes the last alternative. Repeated ports and zero products
are included. The local-affine route uses the supported `01` twist and the
fourth-power invariant to eliminate symmetric off-diagonal entries. It then
constructs actual equality-support phase formulas for both supported diagonal
twists. Thus neither closure properties nor binary normal forms are assumed.

This is a semantic class-closure theorem. It makes no claim about availability
of gadgets, efficient recognition, or tractable evaluation of arbitrary inputs.
-/

namespace Holant.Tractable
noncomputable section

/-- Full Lemma 6.28, for the three genuine source classes and actual invertible
symmetric binary matrices. No class-closure hypothesis is supplied. -/
theorem symmetric_binary_pullback (C : SignatureFamily AlgebraicComplex)
    (hC : C ∈ ({affineClass, productClass, localAffineClass} :
      Set (SignatureFamily AlgebraicComplex)))
    (E F : InvertibleKernel)
    (hE : (⟨2, kernelSignature E.matrix⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hF : (⟨2, kernelSignature F.matrix⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hsE : Kernel.transpose E.matrix = E.matrix)
    (hsF : Kernel.transpose F.matrix = F.matrix) :
    (⟨2, kernelSignature (Kernel.mul (Kernel.mul E.matrix F.matrix) E.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ C := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hC
  rcases hC with rfl | rfl | rfl
  · exact SymmetricBinaryPullback.affine_pullback hE hF
  · exact SymmetricBinaryPullback.product_pullback E F hE hF
  · exact SymmetricBinaryPullback.localAffine_pullback E F hE hF hsE hsF

/-- The same conclusion in the existing edge-pullback notation `Eᵀ F E`. -/
theorem symmetric_binary_kernel_pullback (C : SignatureFamily AlgebraicComplex)
    (hC : C ∈ ({affineClass, productClass, localAffineClass} :
      Set (SignatureFamily AlgebraicComplex)))
    (E F : InvertibleKernel)
    (hE : (⟨2, kernelSignature E.matrix⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hF : (⟨2, kernelSignature F.matrix⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hsE : Kernel.transpose E.matrix = E.matrix)
    (hsF : Kernel.transpose F.matrix = F.matrix) :
    (⟨2, kernelSignature (Kernel.pullback F.matrix E.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ C := by
  simpa only [Kernel.pullback, hsE] using
    symmetric_binary_pullback C hC E F hE hF hsE hsF

/-- Source Lemma 6.28 with nonsingularity expressed directly by the ordinary
two-by-two determinants, without supplying any inverse matrices. -/
theorem symmetric_binary_pullback_of_nonsingular (C : SignatureFamily AlgebraicComplex)
    (hC : C ∈ ({affineClass, productClass, localAffineClass} :
      Set (SignatureFamily AlgebraicComplex)))
    (E F : Kernel AlgebraicComplex)
    (hdetE : SymmetricBinaryPullback.determinant E ≠ 0)
    (hdetF : SymmetricBinaryPullback.determinant F ≠ 0)
    (hE : (⟨2, kernelSignature E⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hF : (⟨2, kernelSignature F⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hsE : Kernel.transpose E = E) (hsF : Kernel.transpose F = F) :
    (⟨2, kernelSignature (Kernel.mul (Kernel.mul E F) E)⟩ :
      AnySignature AlgebraicComplex) ∈ C :=
  symmetric_binary_pullback C hC
    (SymmetricBinaryPullback.invertibleOfDeterminant E hdetE)
    (SymmetricBinaryPullback.invertibleOfDeterminant F hdetF) hE hF hsE hsF

end
end Holant.Tractable
