import Holant.Proofs.Closure.FrontierCurrent
import Holant.Proofs.Closure.FrontierCommonPresentation

/-! Relative closure for the entire CURRENT retained family, including every
newly retained saved prime. The original-only relative conclusion is weaker;
this module exposes the additional current-local leaves explicitly. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.CurrentFrontierClosure
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open CurrentOccurrences FrontierClosure FrontierCommonPresentation
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

structure LocalCurrentTheorems (P : Palette G) (C : AnySignature (OI.K G) → Prop) : Prop where
  unary : ∀ o : Id G P, Domain G P o → (savedLeaf G P o).1.1 = 1 → C (savedLeaf G P o).1
  binary : ∀ o : Id G P, Domain G P o → (savedLeaf G P o).1.1 = 2 → C (savedLeaf G P o).1
  oddNonbinary : ∀ o : Id G P, Domain G P o →
    3 ≤ (savedLeaf G P o).1.1 → Odd (savedLeaf G P o).1.1 → C (savedLeaf G P o).1
  evenNonbinary : ∀ o : Id G P, Domain G P o →
    4 ≤ (savedLeaf G P o).1.1 → Even (savedLeaf G P o).1.1 → C (savedLeaf G P o).1

/-- True stable-state invariants eliminate empty unary domains; they do not
supply a theorem for a genuinely retained unary exit. -/
theorem no_unary_prime_arity (P : Palette G) (noUnary : ¬ RetainedUnary P.family)
    (f : AnySignature (OI.K G)) (retained : f ∈ P.family) (prime : Prime f) : f.1 ≠ 1 := by
  rcases f with ⟨n, f⟩
  intro hn
  dsimp only at hn
  subst n
  exact noUnary ⟨f, retained, prime.1⟩

theorem no_current_unary (P : Palette G) (noUnary : ¬ RetainedUnary P.family)
    (o : Id G P) : (savedLeaf G P o).1.1 ≠ 1 :=
  no_unary_prime_arity G P noUnary (savedLeaf G P o).1
    (savedLeaf_retained G P o) (savedLeaf_prime G P o)

theorem no_current_odd (P : Palette G)
    (noOdd : ∀ f ∈ P.family, Prime f → 3 ≤ f.1 → Even f.1)
    (o : Id G P) (nonbinary : 3 ≤ (savedLeaf G P o).1.1) :
    ¬ Odd (savedLeaf G P o).1.1 := by
  intro odd
  have even := noOdd _ (savedLeaf_retained G P o) (savedLeaf_prime G P o) nonbinary
  rcases even with ⟨k, hk⟩
  rcases odd with ⟨j, hj⟩
  omega

/-- At a genuine stable output the explicit missing membership consumers are
binary and all-even nonbinary leaves. Unary/odd fields follow only from the
actual no-unary/no-odd invariants, not from arbitrary state labels. -/
theorem local_theorems_of_no_unary_no_odd (P : Palette G)
    (C : AnySignature (OI.K G) → Prop) (noUnary : ¬ RetainedUnary P.family)
    (noOdd : ∀ f ∈ P.family, Prime f → 3 ≤ f.1 → Even f.1)
    (binary : ∀ o : Id G P, Domain G P o → (savedLeaf G P o).1.1 = 2 → C (savedLeaf G P o).1)
    (evenNonbinary : ∀ o : Id G P, Domain G P o →
      4 ≤ (savedLeaf G P o).1.1 → Even (savedLeaf G P o).1.1 → C (savedLeaf G P o).1) :
    LocalCurrentTheorems G P C :=
  ⟨fun o _ hn => False.elim (no_current_unary G P noUnary o hn), binary,
    fun o _ hn ho => False.elim (no_current_odd G P noOdd o hn ho), evenNonbinary⟩

theorem leaf_conclusion (P : Palette G) (C : AnySignature (OI.K G) → Prop)
    (leaves : LocalCurrentTheorems G P C) (o : Id G P) : C (savedLeaf G P o).1 := by
  let d := domain G P o
  cases d.kind with
  | unary h => exact leaves.unary o d h
  | binary h => exact leaves.binary o d h
  | oddNonbinary hn ho => exact leaves.oddNonbinary o d hn ho
  | evenNonbinary hn he => exact leaves.evenNonbinary o d hn he

/-- Actual CURRENT-family reconstruction from every current saved prime domain. -/
theorem relative_current_closure (P : Palette G) (C : AnySignature (OI.K G) → Prop)
    (splits : SplitClosed G C) (leaves : LocalCurrentTheorems G P C) :
    ∀ f ∈ P.family, C f := by
  rintro _ ⟨i, rfl⟩
  apply factorTree_closed G C splits (P.trees i)
  intro p
  exact leaf_conclusion G P C leaves ⟨i, p⟩

def currentFamily (P : Palette G) : SignatureFamily AlgebraicComplex := embed G '' P.family

theorem currentFamily_finite (P : Palette G) : (currentFamily G P).Finite :=
  (Set.finite_range _).image (embed G)

/-- Precise relative CURRENT-family common presentation. One actual basis is
shared by all old and new leaves and the mandatory transformed edge. -/
theorem relative_current_common_presentation (P : Palette G)
    (C : SignatureFamily AlgebraicComplex) (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ C)
    (splits : SplitClosed G (leafPredicate G C B))
    (leaves : LocalCurrentTheorems G P (leafPredicate G C B)) :
    CommonTransformable C (currentFamily G P) := by
  refine ⟨currentFamily_finite G P, B, edge, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact relative_current_closure G P (leafPredicate G C B) splits leaves f hf

theorem relative_current_common_k_presentation (P : Palette G)
    (C : SignatureFamily AlgebraicComplex) (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ C)
    (splits : SplitClosed G (leafPredicate G C B))
    (leaves : LocalCurrentTheorems G P (leafPredicate G C B)) :
    CommonKPresentation C (currentFamily G P) :=
  (commonTransformable_iff_commonKPresentation C (currentFamily G P)).mp
    (relative_current_common_presentation G P C B edge splits leaves)

/-- Source structural criterion under the separately named CURRENT-local
leaf hypotheses. No evaluator or complexity theorem is asserted. -/
theorem relative_current_tractx_criterion (P : Palette G) (target : TargetClass)
    (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ target.family)
    (splits : SplitClosed G (leafPredicate G target.family B))
    (leaves : LocalCurrentTheorems G P (leafPredicate G target.family B)) :
    TractX (currentFamily G P) := by
  have common := relative_current_common_presentation G P target.family B edge splits leaves
  have commonPre : CommonTransformable target.family (preprocess (currentFamily G P)) :=
    common.mono_family (fun _ hf => hf.1)
  refine ⟨(currentFamily_finite G P).subset (fun _ hf => hf.1), ?_⟩
  cases target with
  | affine => exact Or.inr (Or.inl commonPre)
  | product => exact Or.inr (Or.inr (Or.inl commonPre))
  | localAffine => exact Or.inr (Or.inr (Or.inr commonPre))

/-- Common presentations restrict along the actual original-root retention;
no new per-original-signature basis is chosen. -/
theorem relative_current_common_restricts_original (P : Palette G)
    (C : SignatureFamily AlgebraicComplex) (B : InvertibleKernel)
    (edge : (⟨2, kernelSignature (Kernel.pullback Signature.equality B.matrix)⟩ :
      AnySignature AlgebraicComplex) ∈ C)
    (splits : SplitClosed G (leafPredicate G C B))
    (leaves : LocalCurrentTheorems G P (leafPredicate G C B)) :
    CommonTransformable C (originalFamily G) := by
  apply (relative_current_common_presentation G P C B edge splits leaves).mono_family
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨f, original_family_retained G P hf, rfl⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.CurrentFrontierClosure
end
