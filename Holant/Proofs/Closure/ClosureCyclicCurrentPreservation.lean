import Holant.Proofs.Closure.ClosureCyclicCurrentInstalled
import Holant.Proofs.Closure.OccurrenceCurrent

/-! Additive occurrence-preserving literal label maps for the installed cyclic
continuation. The whole old tree equality transports its exact dependent leaf
address; duplicate equal-valued roots/leaves remain distinct. No value-level
originalSaved choice or new factorization is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

namespace PowerPalette
/-- Dense old labels keep their original integer identity. -/
theorem oldLabel_injective : Function.Injective (oldLabel G P) := by
  intro i j equal
  apply Fin.ext
  exact congrArg (fun k : Fin (count G P) => k.val) equal
end PowerPalette

variable {m : ℕ} (d : CyclicBoundary.NonsquareExit.DoubledOutside
  (RingHomRealization.mapFamily (ClosurePhysicalBridge.complexEmbedding G) P.family) m)

theorem installedOldLabel_injective : Function.Injective (installedOldLabel G P d) := by
  unfold installedOldLabel squareOldLabel
  exact (PowerPalette.oldLabel_injective G (doubledPalette G P d)).comp
    (RetainedFactorCatalogue.oldLabel_injective G P (squareOriginal G P d) (squareNonzero G P d))

/-- The actual integer-root map plus exact old saved branch address. -/
def installedOldId (o : CurrentOccurrences.Id G P) : CurrentOccurrences.Id G (installedPalette G P d) :=
  ⟨installedOldLabel G P d o.1,Occurrences.transportAddress (installed_old_saved G P d o.1).symm o.2⟩

@[simp] theorem installedOldId_label (o : CurrentOccurrences.Id G P) :
    (installedOldId G P d o).1 = installedOldLabel G P d o.1 := rfl
@[simp] theorem installedOldId_address (o : CurrentOccurrences.Id G P) :
    (installedOldId G P d o).2 = Occurrences.transportAddress (installed_old_saved G P d o.1).symm o.2 := rfl

/-- Equality of the WHOLE literal TreeOccurrence, including prime tree data. -/
theorem installedOldId_leaf (o : CurrentOccurrences.Id G P) :
    CurrentOccurrences.savedLeaf G (installedPalette G P d) (installedOldId G P d o) =
      CurrentOccurrences.savedLeaf G P o :=
  Occurrences.transportAddress_leaf (installed_old_saved G P d o.1).symm o.2

theorem installedOldId_injective : Function.Injective (installedOldId G P d) := by
  rintro ⟨i,p⟩ ⟨j,q⟩ equal
  have hi : installedOldLabel G P d i = installedOldLabel G P d j := congrArg Sigma.fst equal
  have hij := installedOldLabel_injective G P d hi
  subst j
  have hp : Occurrences.transportAddress (installed_old_saved G P d i).symm p =
      Occurrences.transportAddress (installed_old_saved G P d i).symm q :=
    @sigma_mk_injective (Fin (installedPalette G P d).count)
      (fun k => Occurrences.Address ((installedPalette G P d).trees k))
      (installedOldLabel G P d i) _ _ equal
  exact Sigma.ext rfl (heq_of_eq (Occurrences.transportAddress_injective (installed_old_saved G P d i).symm hp))

/-- Explicit ordered Boolean branch word for a saved prime address. -/
def branchPath {L : Type*} [Field L] {f : AnySignature L} (tree : FactorTree f) : Occurrences.Address tree → List Bool :=
  match tree with
  | .leaf _ _ => fun _ => []
  | .split _ left right => Sum.elim (fun p => false :: branchPath left p) (fun p => true :: branchPath right p)

theorem transportAddress_path {L : Type*} [Field L] {u v : TreeOccurrence L} (same : u = v)
    (p : Occurrences.Address u.2) :
    branchPath v.2 (Occurrences.transportAddress same p) = branchPath u.2 p := by
  cases same
  rfl

theorem installedOldId_path (o : CurrentOccurrences.Id G P) :
    branchPath ((installedPalette G P d).trees (installedOldId G P d o).1) (installedOldId G P d o).2 =
      branchPath (P.trees o.1) o.2 :=
  transportAddress_path (installed_old_saved G P d o.1).symm o.2

/-- Root and address injection preserve physically repeated leaf occurrences. -/
theorem installed_duplicate_addresses (i : Fin P.count)
    (p q : Occurrences.Address (P.trees i)) (different : p ≠ q) :
    installedOldId G P d ⟨i,p⟩ ≠ installedOldId G P d ⟨i,q⟩ := by
  intro equal
  have idEqual := installedOldId_injective G P d equal
  exact different (@sigma_mk_injective (Fin P.count) (fun j => Occurrences.Address (P.trees j)) i p q idEqual)
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCyclicCurrent
