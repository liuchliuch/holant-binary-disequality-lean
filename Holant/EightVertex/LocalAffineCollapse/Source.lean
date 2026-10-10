import Holant.EightVertex.LocalAffineCollapse.AlgebraicWitness

/-! Source Lemma 4.4. The original matrix may have arbitrary complex entries.
The classes A and L contain algebraic signatures, as in the manuscript's
signature convention. Their occurrences inside a complex coordinate space are
represented by exact coefficient embedding, not by a restriction on the basis.
The stronger core also permits the zero input; the source wrapper retains the
paper's nonzero assumption. -/
namespace Holant.EightVertex.LocalAffineCollapse
open Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The literal algebraic signature class viewed in the complex coefficient space. -/
def ComplexAffine {n : ℕ} (f : Signature ℂ n) : Prop :=
  ∃g : Signature AlgebraicComplex n, Affine g ∧ embedSignature g=f

def ComplexLocalAffine {n : ℕ} (f : Signature ℂ n) : Prop :=
  ∃g : Signature AlgebraicComplex n, LocalAffine g ∧ embedSignature g=f

def complexKernelSignature (E : Kernel ℂ) : Signature ℂ 2 := fun x => E (x 0) (x 1)

theorem kernel_model_iff (E : Kernel ℂ) :
    ComplexLocalAffine (complexKernelSignature E) ↔
      ∃e : Kernel AlgebraicComplex, LocalAffine (kernelSignature e) ∧ embedMatrix e=E := by
  constructor
  · rintro ⟨g,hg,he⟩
    let e : Kernel AlgebraicComplex := fun a b => g ![a,b]
    have heq : kernelSignature e=g := by
      funext x
      apply congrArg g
      funext i
      fin_cases i <;> rfl
    refine ⟨e,heq ▸ hg,?_⟩
    funext a b
    exact congrFun he ![a,b]
  · rintro ⟨e,he,heq⟩
    refine ⟨kernelSignature e,he,?_⟩
    funext x
    exact congrFun (congrFun heq (x 0)) (x 1)

theorem affine_kernel_model (e : Kernel AlgebraicComplex) (E : Kernel ℂ)
    (he : Affine (kernelSignature e)) (heq : embedMatrix e=E) :
    ComplexAffine (complexKernelSignature E) := by
  refine ⟨kernelSignature e,he,?_⟩
  funext x
  exact congrFun (congrFun heq (x 0)) (x 1)

/-- The complex witness is replaced by deletion of a derived algebraic eighth-root
column phase. This statement has no algebraicity assumption on T or M. -/
theorem complex_local_affine_collapse (T : ComplexBasis) (M : Signature ℂ 4)
    (hM : ∀x,Holant.weight x%2=1 → M x=0)
    (hE : ComplexLocalAffine (complexKernelSignature (Kernel.pullback Signature.disequality T.matrix)))
    (hN : ComplexLocalAffine (T.symm.action M)) :
    ∃T0 : ComplexBasis,
      ComplexAffine (complexKernelSignature (Kernel.pullback Signature.disequality T0.matrix)) ∧
      ComplexAffine (T0.symm.action M) := by
  obtain ⟨E,hEL,hEeq⟩ := (kernel_model_iff _).mp hE
  obtain ⟨N,hNL,hNeq⟩ := hN
  obtain ⟨rho,hr,_hr8,hA,hN0,hE0⟩ := phase_reduction T E hEeq hEL M hM N hNeq hNL
  exact ⟨removeColumnPhase T rho hr,
    affine_kernel_model _ _ (affine_removed_edge (E false false)) hE0,
    ⟨raised N rho,hA,hN0⟩⟩

/-- The original numbered statement, with both edge and signature transformed
by the same actual invertible matrix and with the source nonzero hypothesis. -/
theorem source_local_affine_reduction (M : Signature ℂ 4) (_hM0 : M≠0)
    (hM : ∀x,Holant.weight x%2=1 → M x=0) (T : ComplexBasis)
    (hE : ComplexLocalAffine (complexKernelSignature (Kernel.pullback Signature.disequality T.matrix)))
    (hN : ComplexLocalAffine (T.symm.action M)) :
    ∃T0 : ComplexBasis,
      ComplexAffine (complexKernelSignature (Kernel.pullback Signature.disequality T0.matrix)) ∧
      ComplexAffine (T0.symm.action M) := complex_local_affine_collapse T M hM hE hN

/-- The algebraic clause uses a genuine algebraic inverse and returns an
algebraic matrix, rather than asserting algebraic coordinates of a complex witness. -/
theorem source_algebraic_local_affine_reduction (M : Signature AlgebraicComplex 4)
    (_hM0 : M≠0) (hM : ∀x,Holant.weight x%2=1 → M x=0) (T : InvertibleKernel)
    (hE : LocalAffine (kernelSignature (Kernel.pullback Signature.disequality T.matrix)))
    (hN : LocalAffine (T.symm.action M)) :
    ∃T0 : InvertibleKernel,
      Affine (kernelSignature (Kernel.pullback Signature.disequality T0.matrix)) ∧
      Affine (T0.symm.action M) := by
  obtain ⟨rho,hr,_hr8,hA,hN0⟩ := algebraic_phase_reduction T M hM hE hN
  exact ⟨algebraicRemove T rho hr,hA,hN0⟩

/-- The matrix representation is exactly GL(2,C): determinant nonzero is
sufficient, and every returned basis has nonzero determinant. -/
theorem source_matrix_local_affine_reduction (A : Kernel ℂ) (hA : complexDet A≠0)
    (M : Signature ℂ 4) (hM : ∀x,Holant.weight x%2=1 → M x=0)
    (hE : ComplexLocalAffine (complexKernelSignature (Kernel.pullback Signature.disequality A)))
    (hN : ComplexLocalAffine ((basisOfDet A hA).symm.action M)) :
    ∃T0 : ComplexBasis, complexDet T0.matrix≠0 ∧
      ComplexAffine (complexKernelSignature (Kernel.pullback Signature.disequality T0.matrix)) ∧
      ComplexAffine (T0.symm.action M) := by
  obtain ⟨T0,hE0,hN0⟩ := complex_local_affine_collapse (basisOfDet A hA) M hM hE hN
  exact ⟨T0,complexDet_ne_zero T0,hE0,hN0⟩

end
end Holant.EightVertex.LocalAffineCollapse
