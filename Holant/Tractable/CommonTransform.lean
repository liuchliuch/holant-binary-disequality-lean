import Holant.Tractable.Affine
import Holant.Tractable.Product
import Holant.Tractable.LocalAffine
import Holant.Realization

/-!
Common transformability, source `def:common-transformability` (lines 2098ff).
The outer witness is ONE actual invertible two-by-two matrix, shared by the edge
and every signature of the family. Both inverse identities are included, so the
witness is exactly an element of `GL₂` represented using Boolean-indexed kernels.
Finiteness is explicit. Predicates do not assert tractability or recognition.
-/

namespace Holant.Tractable

noncomputable section

/-- Turn a Boolean-indexed binary table into the existing two-port signature type. -/
def kernelSignature (E : Kernel AlgebraicComplex) : Signature AlgebraicComplex 2 :=
  fun x => E (x 0) (x 1)

/-- A genuine invertible kernel, with a single shared two-sided inverse. -/
structure InvertibleKernel where
  matrix : Kernel AlgebraicComplex
  inverse : Kernel AlgebraicComplex
  matrix_inverse : Kernel.mul matrix inverse = Signature.equality
  inverse_matrix : Kernel.mul inverse matrix = Signature.equality

namespace InvertibleKernel

def identity : InvertibleKernel :=
  ⟨Signature.equality, Signature.equality, Kernel.equality_mul _, Kernel.equality_mul _⟩

def symm (B : InvertibleKernel) : InvertibleKernel :=
  ⟨B.inverse, B.matrix, B.inverse_matrix, B.matrix_inverse⟩

@[simp] theorem symm_symm (B : InvertibleKernel) : B.symm.symm = B := rfl

@[simp] theorem identity_symm : identity.symm = identity := rfl

/-- Composition of actual invertible matrices; inverses occur in reverse order. -/
def comp (B D : InvertibleKernel) : InvertibleKernel where
  matrix := Kernel.mul B.matrix D.matrix
  inverse := Kernel.mul D.inverse B.inverse
  matrix_inverse := by
    rw [Kernel.mul_assoc, ← Kernel.mul_assoc D.matrix D.inverse B.inverse,
      D.matrix_inverse, Kernel.equality_mul, B.matrix_inverse]
  inverse_matrix := by
    rw [Kernel.mul_assoc, ← Kernel.mul_assoc B.inverse B.matrix D.matrix,
      B.inverse_matrix, Kernel.equality_mul, D.inverse_matrix]

/-- The same matrix acts at every port, with the source's column convention. -/
def action (B : InvertibleKernel) {n : ℕ} (f : Signature AlgebraicComplex n) :
    Signature AlgebraicComplex n := Signature.coordinateAction (fun _ => B.matrix) f

@[simp] theorem identity_action {n : ℕ} (f : Signature AlgebraicComplex n) :
    identity.action f = f := Signature.coordinateAction_equality f

@[simp] theorem action_symm_action (B : InvertibleKernel) {n : ℕ}
    (f : Signature AlgebraicComplex n) : B.action (B.symm.action f) = f :=
  Signature.coordinateAction_cancel _ _ (fun _ => B.matrix_inverse) f

@[simp] theorem symm_action_action (B : InvertibleKernel) {n : ℕ}
    (f : Signature AlgebraicComplex n) : B.symm.action (B.action f) = f :=
  Signature.coordinateAction_cancel _ _ (fun _ => B.inverse_matrix) f

@[simp] theorem comp_action (B D : InvertibleKernel) {n : ℕ}
    (f : Signature AlgebraicComplex n) :
    (B.comp D).action f = B.action (D.action f) :=
  (Signature.coordinateAction_comp _ _ _).symm

@[simp] theorem comp_symm (B D : InvertibleKernel) : (B.comp D).symm = D.symm.comp B.symm := rfl

end InvertibleKernel

def affineClass : SignatureFamily AlgebraicComplex := {f | Affine f.2}
def productClass : SignatureFamily AlgebraicComplex := {f | Product f.2}
def localAffineClass : SignatureFamily AlgebraicComplex := {f | LocalAffine f.2}
def atMostOneClass : SignatureFamily AlgebraicComplex := {f | AtMostOneSupport f.2}

/-- The exact common-basis conditions; the edge is a mandatory member too. -/
def IsCommonBasis (C F : SignatureFamily AlgebraicComplex) (B : InvertibleKernel) : Prop :=
  (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
    AnySignature AlgebraicComplex) ∈ C ∧
  ∀ f ∈ F, (⟨f.1, B.symm.action f.2⟩ : AnySignature AlgebraicComplex) ∈ C

/-- Source common transformability for a finite signature family.
The existential is outside the universal quantifier over all family members. -/
def CommonTransformable (C F : SignatureFamily AlgebraicComplex) : Prop :=
  F.Finite ∧ ∃ B : InvertibleKernel, IsCommonBasis C F B

/-- In already-`K` coordinates, the same witness pulls back the disequality edge.
This is the source's displayed `PresK(K Γ; C)` condition, with no unspecified K. -/
def IsCommonKBasis (C Gamma : SignatureFamily AlgebraicComplex)
    (U : InvertibleKernel) : Prop :=
  (⟨2, kernelSignature (Kernel.pullback Signature.disequality U.matrix)⟩ :
    AnySignature AlgebraicComplex) ∈ C ∧
  ∀ f ∈ Gamma, (⟨f.1, U.symm.action f.2⟩ : AnySignature AlgebraicComplex) ∈ C

/-- Exact `K`-presentation condition for an input already expressed in `K` coordinates. -/
def CommonKPresentationInKCoordinates (C Gamma : SignatureFamily AlgebraicComplex) : Prop :=
  Gamma.Finite ∧ ∃ U : InvertibleKernel, IsCommonKBasis C Gamma U

/-- Restricting the family preserves its common basis, never choosing new per-member bases. -/
theorem CommonTransformable.mono_family {C F G : SignatureFamily AlgebraicComplex}
    (h : CommonTransformable C F) (hGF : G ⊆ F) : CommonTransformable C G := by
  rcases h with ⟨hfin, B, hedge, hf⟩
  exact ⟨hfin.subset hGF, B, hedge, fun f hfg => hf f (hGF hfg)⟩

theorem CommonTransformable.mono_class {C D F : SignatureFamily AlgebraicComplex}
    (h : CommonTransformable C F) (hCD : C ⊆ D) : CommonTransformable D F := by
  rcases h with ⟨hfin, B, hedge, hf⟩
  exact ⟨hfin, B, hCD hedge, fun f hff => hCD (hf f hff)⟩

/-- Membership in a class with equality gives the literal identity common basis. -/
theorem commonTransformable_identity {C F : SignatureFamily AlgebraicComplex}
    (hfin : F.Finite)
    (hedge : (⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex) ∈ C)
    (hf : F ⊆ C) : CommonTransformable C F := by
  refine ⟨hfin, InvertibleKernel.identity, ?_, ?_⟩
  · simpa [InvertibleKernel.identity, Kernel.pullback] using hedge
  · intro f hff
    simpa using hf hff

end
end Holant.Tractable
