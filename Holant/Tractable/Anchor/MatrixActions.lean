import Holant.Tractable.SourceCorrespondence

/-!
Exact source-coordinate identities for the two literal binary anchors.
All actions are the full ordered tensor action on both ports, over the actual
algebraic-complex field, with ordinary transpose and no conjugation.
-/

namespace Holant.Tractable
noncomputable section

/-- The two Boolean diagonal entries, with both off-diagonal entries zero. -/
def diagonalKernel (a b : AlgebraicComplex) : Kernel AlgebraicComplex :=
  fun x y => if x = y then (if x then b else a) else 0

/-- The literal binary disequality anchor `X`. -/
def xAnchor : Signature AlgebraicComplex 2 := kernelSignature Signature.disequality

/-- The literal binary phase anchor `Z = diag(1,-1)`. -/
def zAnchor : Signature AlgebraicComplex 2 := kernelSignature (diagonalKernel 1 (-1))

/-- The bit-flip kernel is its own certified two-sided inverse. -/
def bitFlipBasis : InvertibleKernel :=
  ⟨Signature.disequality, Signature.disequality,
    Kernel.disequality_mul_disequality, Kernel.disequality_mul_disequality⟩

@[simp] theorem bitFlipBasis_symm : bitFlipBasis.symm = bitFlipBasis := rfl

/-- Uniform action of `X` complements every input bit, including at arity zero. -/
@[simp] theorem bitFlipBasis_action {n : ℕ} (f : Signature AlgebraicComplex n)
    (x : Fin n → Bool) : bitFlipBasis.action f x = f (fun j => !(x j)) := by
  have hflip (a b : Bool) : Signature.disequality (K := AlgebraicComplex) a b =
      Signature.equality (!a) b := by cases a <;> cases b <;> rfl
  simp [InvertibleKernel.action, bitFlipBasis, Signature.coordinateAction,
    hflip, Signature.prod_equality]

/-- On a binary table, the uniform tensor action is ordinary matrix sandwiching. -/
theorem coordinateAction_kernelSignature (A E : Kernel AlgebraicComplex) :
    Signature.coordinateAction (fun _ : Fin 2 => A) (kernelSignature E) =
      kernelSignature (Kernel.mul (Kernel.mul A E) (Kernel.transpose A)) := by
  funext x
  unfold Signature.coordinateAction
  rw [← (piFinTwoEquiv (fun _ : Fin 2 => Bool)).symm.sum_comp]
  simp [Fintype.sum_prod_type, Fin.prod_univ_two, kernelSignature,
    Kernel.mul_apply, Kernel.transpose, piFinTwoEquiv]
  ring

/-- Flipping both ports exchanges the two endpoint values of a diagonal signature. -/
@[simp] theorem bitFlipBasis_action_diagonalKernel (a b : AlgebraicComplex) :
    bitFlipBasis.action (kernelSignature (diagonalKernel a b)) =
      kernelSignature (diagonalKernel b a) := by
  funext x
  rw [bitFlipBasis_action]
  have hflip (p q : Bool) : diagonalKernel a b (!p) (!q) =
      diagonalKernel b a p q := by cases p <;> cases q <;> rfl
  exact hflip (x 0) (x 1)

/-- Binary equality is invariant under complementing both endpoints. -/
@[simp] theorem bitFlipBasis_action_equality :
    bitFlipBasis.action (kernelSignature Signature.equality) =
      kernelSignature Signature.equality := by
  funext x
  rw [bitFlipBasis_action]
  have hflip (p q : Bool) : Signature.equality (K := AlgebraicComplex) (!p) (!q) =
      Signature.equality p q := by cases p <;> cases q <;> rfl
  exact hflip (x 0) (x 1)

/-- Inverse source `K` on both ports sends the literal `X` anchor to `diag(-i,i)`. -/
theorem sourceKBasis_symm_action_xAnchor :
    sourceKBasis.symm.action xAnchor =
      kernelSignature (diagonalKernel (-imaginaryUnit) imaginaryUnit) := by
  rw [xAnchor, InvertibleKernel.action, coordinateAction_kernelSignature]
  congr 1
  funext a b
  cases a <;> cases b <;>
    simp [sourceKBasis, InvertibleKernel.symm, Kernel.mul_apply, Kernel.transpose,
      KInverse, diagonalKernel, Signature.disequality] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq, inv_pow, sqrtTwo_sq] <;> ring

/-- Inverse source `K` on both ports sends the literal `Z` anchor to equality. -/
theorem sourceKBasis_symm_action_zAnchor :
    sourceKBasis.symm.action zAnchor = kernelSignature Signature.equality := by
  rw [zAnchor, InvertibleKernel.action, coordinateAction_kernelSignature]
  congr 1
  funext a b
  cases a <;> cases b <;>
    simp [sourceKBasis, InvertibleKernel.symm, Kernel.mul_apply, Kernel.transpose,
      KInverse, diagonalKernel, Signature.equality,
      div_mul_div_comm, ← pow_two, imaginaryUnit_sq, sqrtTwo_sq] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq, inv_pow, sqrtTwo_sq]

/-- The inverse `KX` action has the same two nonzero endpoint entries in reverse order. -/
theorem sourceKXBasis_symm_action_xAnchor :
    (sourceKBasis.comp bitFlipBasis).symm.action xAnchor =
      kernelSignature (diagonalKernel imaginaryUnit (-imaginaryUnit)) := by
  rw [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
    bitFlipBasis_symm, sourceKBasis_symm_action_xAnchor, bitFlipBasis_action_diagonalKernel]

/-- The inverse `KX` action also sends the literal `Z` anchor to equality. -/
theorem sourceKXBasis_symm_action_zAnchor :
    (sourceKBasis.comp bitFlipBasis).symm.action zAnchor =
      kernelSignature Signature.equality := by
  rw [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
    bitFlipBasis_symm, sourceKBasis_symm_action_zAnchor, bitFlipBasis_action_equality]

end
end Holant.Tractable
