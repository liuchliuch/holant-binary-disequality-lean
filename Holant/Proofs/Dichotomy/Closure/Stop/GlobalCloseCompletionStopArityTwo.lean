import Holant.Proofs.Closure.FrontierSmallArity
import Holant.Proofs.Dichotomy.Retained.StablePaletteTractability

/-! A genuine terminal consumer at any actual structural-stop palette.
The exact saved forest is scanned without refactorization. If no higher leaf
is present, its proved tensor decomposition supplies the implemented native
algorithm and the original-G answer codec. Otherwise the selected immutable
higher occurrence is retained, including its actual source access. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopArityTwo
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

abbrev OriginalProgramme := BinaryCompose.Computes
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)

abbrev OriginalFP := InFP
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
  (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G)

/-- No whole-family classification hypothesis is required: the actual empty
saved-leaf scan reconstructs the native tensor criterion internally. -/
def programme (empty : FrontierSmallArity.scan G P = none) : OriginalProgramme G :=
  StablePaletteTractability.originalComputes G P
    (FrontierSmallArity.small_native_tractX G P empty)

theorem inFP (empty : FrontierSmallArity.scan G P = none) : OriginalFP G :=
  (programme G P empty).inFP

theorem resources (empty : FrontierSmallArity.scan G P = none)
    (r : EdgeSubdivision.WireEquivalence.Input s a) :
    Holant.LocalDrafts.RemoteWork.TractChainV1.InstalledResources.Contract
      (programme G P empty) r :=
  Holant.LocalDrafts.RemoteWork.TractChainV1.InstalledResources.receipt _ _

/-- Every returned large slot is a real retained prime with exact original
field coefficients. Its existence is not renamed a hard outcome. -/
theorem large_retained (d : FrontierSmallArity.Large G P) :
    (CurrentOccurrences.savedLeaf G P d.id).1 ∈ P.family ∧
    Holant.LocalDrafts.FinitePGL2.Stabilization.Prime
      (CurrentOccurrences.savedLeaf G P d.id).1 ∧
    3 ≤ (CurrentOccurrences.savedLeaf G P d.id).1.1 :=
  ⟨CurrentOccurrences.savedLeaf_retained G P d.id,
    CurrentOccurrences.savedLeaf_prime G P d.id,d.nonbinary⟩

inductive Completion : Type 1 where
  | small (empty : FrontierSmallArity.scan G P = none)
      (evaluator : OriginalProgramme G)
  | higher (data : FrontierSmallArity.Large G P)

/-- The evaluator in the small arm is installed in the same branch in which
the exact forest scan proves its hypothesis. No evaluator is an input. -/
def complete : Completion G P :=
  match FrontierSmallArity.inspect G P with
  | .small empty _ => .small empty (programme G P empty)
  | .large data => .higher data

theorem outcome : OriginalFP G ∨ Nonempty (FrontierSmallArity.Large G P) := by
  cases complete G P with
  | small empty evaluator => exact Or.inl evaluator.inFP
  | higher data => exact Or.inr ⟨data⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopArityTwo
end
