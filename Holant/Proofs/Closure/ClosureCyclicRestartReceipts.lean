import Holant.Proofs.Closure.ClosureCyclicRestartDispatch

/-! Exact copied-tree and physical terminal receipts for the repeated protocol.
Every terminal augmentation preserves the literal old roots, not just values. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

def projectiveCopy (P : Palette G) {n : ℕ} (target : Signature ℂ n)
    (output : ClosureCyclicCurrent.ProjectiveOutput G P target)
    (positive : 0 < n) (nonzero : target ≠ 0) :
    Copy G P (ClosureCyclicCurrent.ProjectiveOutput.palette G P target output positive nonzero) :=
  ⟨RetainedFactorCatalogue.oldLabel G P
      ⟨n,ClosureCyclicCurrent.ProjectiveOutput.output G P target output⟩
      (ClosureCyclicCurrent.ProjectiveOutput.source_nonzero G P target output nonzero),
    RetainedFactorCatalogue.oldLabel_injective G P
      ⟨n,ClosureCyclicCurrent.ProjectiveOutput.output G P target output⟩
      (ClosureCyclicCurrent.ProjectiveOutput.source_nonzero G P target output nonzero),
    ClosureCyclicCurrent.ProjectiveOutput.old_saved G P target output positive nonzero⟩

def Terminal.palette {S : Node G} : Terminal G S → Palette G
  | .noncyclic _ => S.palette
  | .small _ _ => S.palette
  | .endpoint _ _ receipt _ => ClosureCyclicCurrent.EndpointReceipt.palette G S.palette receipt
  | .unary _ _ receipt _ _ _ => ClosureCyclicCurrent.OutsideReceipt.palette G S.palette receipt
  | .installedStop _ _ receipt _ _ _ => ClosureCyclicCurrent.installedPalette G S.palette receipt.doubled
  | .preparedOther growth _ => growth.finalPalette

def Terminal.copy {S : Node G} (terminal : Terminal G S) : Copy G S.palette (terminal.palette G) := by
  cases terminal with
  | noncyclic _ => exact Copy.identity S.palette
  | small _ _ => exact Copy.identity S.palette
  | endpoint _ _ receipt _ =>
      exact projectiveCopy G S.palette receipt.target receipt.access (by norm_num)
        (ClosureCyclicCurrent.EndpointReceipt.target_nonzero G S.palette receipt)
  | unary _ _ receipt _ _ _ =>
      exact projectiveCopy G S.palette receipt.card.signature receipt.access (by norm_num) receipt.card.nonzero
  | installedStop _ _ receipt _ _ _ =>
      exact ⟨ClosureCyclicCurrent.installedOldLabel G S.palette receipt.doubled,
        ClosureCyclicCurrent.installedOldLabel_injective G S.palette receipt.doubled,
        ClosureCyclicCurrent.installed_old_saved G S.palette receipt.doubled⟩
  | preparedOther growth _ => exact growth.copy

abbrev Terminal.toOriginal {S : Node G} (terminal : Terminal G S) := (terminal.palette G).toOriginal
abbrev Terminal.fromOriginal {S : Node G} (terminal : Terminal G S) := (terminal.palette G).fromOriginal

def Terminal.toOriginal_prefix_costs {S : Node G} (terminal : Terminal G S) :=
  (terminal.toOriginal G).primitives
def Terminal.toOriginal_transcript_bits {S : Node G} (terminal : Terminal G S) :=
  (terminal.toOriginal G).transcriptBits
def Terminal.toOriginal_prefix_storage {S : Node G} (terminal : Terminal G S) :=
  (terminal.toOriginal G).storage
def Terminal.fromOriginal_prefix_costs {S : Node G} (terminal : Terminal G S) :=
  (terminal.fromOriginal G).primitives
def Terminal.fromOriginal_transcript_bits {S : Node G} (terminal : Terminal G S) :=
  (terminal.fromOriginal G).transcriptBits
def Terminal.fromOriginal_prefix_storage {S : Node G} (terminal : Terminal G S) :=
  (terminal.fromOriginal G).storage

theorem Copy.occurrence_path {P Q : Palette G} (copy : Copy G P Q) (o : CurrentOccurrences.Id G P) :
    ClosureCyclicCurrent.branchPath (Q.trees (copy.occurrence o).1) (copy.occurrence o).2 =
      ClosureCyclicCurrent.branchPath (P.trees o.1) o.2 :=
  ClosureCyclicCurrent.transportAddress_path (copy.saved o.1).symm o.2

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicRestart
end
