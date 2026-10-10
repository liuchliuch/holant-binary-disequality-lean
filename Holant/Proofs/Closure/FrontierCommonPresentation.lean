import Holant.Proofs.Closure.FrontierClosure
import Holant.Tractable.Criteria

/-! Concrete relative common-presentation consumers of the source frontier.
The same actual basis and target class are shared by every original occurrence.
Local leaf membership, the mandatory transformed edge and the local split rule
remain explicit hypotheses. No unconditional classification or complexity
result is inferred from a minimum-core structural exit. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierCommonPresentation
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Occurrences Frontier FrontierClosure

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

/-- The literal original-field embedding, not a re-extracted coefficient field. -/
def embed (f : AnySignature (OI.K G)) : AnySignature AlgebraicComplex :=
  ⟨f.1, fun x => Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.embedding G (f.2 x)⟩

def originalFamily : SignatureFamily AlgebraicComplex := embed G '' OI.family G

theorem originalFamily_finite : (originalFamily G).Finite := by
  apply Set.Finite.image
  rw [← Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput.family_exact G]
  exact Set.finite_range _

/-- One B and C occur outside the universal over original saved prime addresses. -/
def leafPredicate (C : SignatureFamily AlgebraicComplex) (B : InvertibleKernel)
    (f : AnySignature (OI.K G)) : Prop :=
  (⟨f.1, B.symm.action (embed G f).2⟩ : AnySignature AlgebraicComplex) ∈ C

/-- Precise relative whole-saved-family common-basis conclusion, including the
mandatory equality-edge pullback. The local leaf and split hypotheses are the
explicit external theorem boundary, not a whole-family closure certificate. -/
theorem relative_common_presentation (P : Palette G)
    (C : SignatureFamily AlgebraicComplex) (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ C)
    (splits : SplitClosed G (leafPredicate G C B))
    (leaves : LocalLeafTheorems G P (leafPredicate G C B)) :
    CommonTransformable C (originalFamily G) := by
  refine ⟨originalFamily_finite G, B, edge, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact relative_saved_closure G P (leafPredicate G C B) splits leaves f hf

/-- The frozen ordinary-table CommonKPresentation criterion follows by the
proved single-shared-basis correspondence, under the same local leaves. The
native-X computational family is its forward-K image; the native criterion is
separately supplied by FrontierNativeClosure, including its disequality edge. -/
theorem relative_common_k_presentation (P : Palette G)
    (C : SignatureFamily AlgebraicComplex) (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ C)
    (splits : SplitClosed G (leafPredicate G C B))
    (leaves : LocalLeafTheorems G P (leafPredicate G C B)) :
    CommonKPresentation C (originalFamily G) :=
  (commonTransformable_iff_commonKPresentation C (originalFamily G)).mp
    (relative_common_presentation G P C B edge splits leaves)

/-- Source-defined target classes; local-affine is never upgraded to affine. -/
inductive TargetClass where
  | affine
  | product
  | localAffine

def TargetClass.family : TargetClass → SignatureFamily AlgebraicComplex
  | .affine => affineClass
  | .product => productClass
  | .localAffine => localAffineClass

/-- Concrete relative structural TractX criterion, not an evaluator or hardness
claim. Its local theorem hypotheses must still be proved at every listed domain. -/
theorem relative_tractx_criterion (P : Palette G) (target : TargetClass)
    (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (splits : SplitClosed G (leafPredicate G target.family B))
    (leaves : LocalLeafTheorems G P (leafPredicate G target.family B)) :
    TractX (originalFamily G) := by
  have common := relative_common_presentation G P target.family B edge splits leaves
  have commonPre : CommonTransformable target.family (preprocess (originalFamily G)) :=
    common.mono_family (fun _ hf => hf.1)
  refine ⟨(originalFamily_finite G).subset (fun _ hf => hf.1), ?_⟩
  cases target with
  | affine => exact Or.inr (Or.inl commonPre)
  | product => exact Or.inr (Or.inr (Or.inl commonPre))
  | localAffine => exact Or.inr (Or.inr (Or.inr commonPre))

end Holant.LocalDrafts.RemoteWork.StableClosureV2.FrontierCommonPresentation
end
