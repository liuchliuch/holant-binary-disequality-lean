import Holant.Proofs.Dichotomy.Closure.Native.GlobalCloseCompletionNativeMContinuation

/-! The surviving higher branch has PROVED simultaneous induction bases.
Its one returned identity basis covers every binary and every q4 saved leaf;
the absence of dense q4 is established by the actual earlier continuation.
Only the mathematical higher-ancestor implication remains to be supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionHigherBases
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open FrontierCommonPresentation
open GlobalCloseCompletionMixedCurrent
open GlobalCloseCompletionNativeMContinuation (classFamily)
set_option backward.isDefEq.respectTransparency false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (base : Palette G)
variable {A : GeneratedGroupWorklist.Active G base}
variable (R : GeneratedGroupWorklist.Exhausted G base A)
variable (C : EOClass)
variable (basis : IsCommonKBasis (classFamily C) (family G base R) InvertibleKernel.identity)

include basis in
theorem binary (o : CurrentOccurrences.Id G (palette G base R))
    (two : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=2) :
    leafPredicate G (classFamily C) InvertibleKernel.identity
      (CurrentOccurrences.savedLeaf G (palette G base R) o).1 :=
  basis.2 _ (complete G base R o (Or.inl two))

include basis in
theorem quaternary (noDense : ¬Dense G base R) (o : CurrentOccurrences.Id G (palette G base R))
    (four : (CurrentOccurrences.savedLeaf G (palette G base R) o).1.1=4) :
    leafPredicate G (classFamily C) InvertibleKernel.identity
      (CurrentOccurrences.savedLeaf G (palette G base R) o).1 := by
  apply basis.2 _ (complete G base R o (Or.inr ⟨four,?_⟩))
  rintro ⟨p,hp⟩
  exact noDense ⟨o,four,p,hp⟩

include basis in
theorem native_edge :
    (⟨2,kernelSignature (Kernel.pullback Signature.disequality InvertibleKernel.identity.matrix)⟩ :
      AnySignature AlgebraicComplex)∈classFamily C := basis.1

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionHigherBases
end
